#!/usr/bin/env python3
"""Verify genuine extracted bytes and selected method Code pins, offline."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import zipfile

HERE = Path(__file__).resolve().parent


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


class Reader:
    def __init__(self, raw):
        self.raw, self.at = raw, 0

    def take(self, count):
        if count < 0 or self.at + count > len(self.raw):
            raise ValueError("truncated class/attribute")
        begin = self.at
        self.at += count
        return self.raw[begin:self.at]

    def u(self, count):
        return int.from_bytes(self.take(count), "big")

    def end(self):
        if self.at != len(self.raw):
            raise ValueError("trailing class/attribute bytes")


def class_methods(raw):
    r = Reader(raw)
    if r.u(4) != 0xCAFEBABE:
        raise ValueError("class magic")
    r.take(4)
    cp, count = [None], r.u(2)
    while len(cp) < count:
        tag = r.u(1)
        if tag == 1:
            cp.append((tag, r.take(r.u(2))))
        elif tag in (3, 4):
            cp.append((tag, r.take(4)))
        elif tag in (5, 6):
            cp.extend([(tag, r.take(8)), None])
        elif tag in (7, 8, 16, 19, 20):
            cp.append((tag, r.u(2)))
        elif tag in (9, 10, 11, 12, 17, 18):
            cp.append((tag, r.take(4)))
        elif tag == 15:
            cp.append((tag, r.take(3)))
        else:
            raise ValueError("unsupported constant pool tag")
    if len(cp) != count:
        raise ValueError("constant pool size")

    def utf(index):
        if not 0 < index < len(cp) or cp[index] is None or cp[index][0] != 1:
            raise ValueError("UTF reference")
        # Only ASCII owner/method/descriptor/attribute names are requested.
        return cp[index][1].decode("ascii")

    def cls(index):
        if not 0 < index < len(cp) or cp[index] is None or cp[index][0] != 7:
            raise ValueError("class reference")
        return utf(cp[index][1])

    r.take(2)
    owner = cls(r.u(2))
    r.take(2)
    r.take(2 * r.u(2))

    def attributes(reader):
        result = []
        for _ in range(reader.u(2)):
            name = utf(reader.u(2))
            result.append((name, reader.take(reader.u(4))))
        return result

    for _ in range(r.u(2)):
        r.take(6)
        attributes(r)
    methods = {}
    for _ in range(r.u(2)):
        flags, name, descriptor = r.u(2), utf(r.u(2)), utf(r.u(2))
        key = name, descriptor
        if key in methods:
            raise ValueError("duplicate method ABI")
        attrs = attributes(r)
        codes = [value for tag, value in attrs if tag == "Code"]
        if len(codes) > 1 or bool(codes) == bool(flags & (0x0100 | 0x0400)):
            raise ValueError("method Code/flags mismatch")
        row = {"flags": flags, "code_present": bool(codes)}
        if codes:
            code = Reader(codes[0])
            code.take(4)
            body = code.take(code.u(4))
            handlers = code.u(2)
            for _ in range(handlers):
                start, end, target, catch = [code.u(2) for _ in range(4)]
                if not 0 <= start < end <= len(body) or target >= len(body):
                    raise ValueError("exception range")
                if catch:
                    cls(catch)
            attributes(code)
            code.end()
            row.update(code_bytes=len(body), code_sha256=sha(body))
        methods[key] = row
    attributes(r)
    r.end()
    return owner, methods


def check_method(row, actual):
    key = row["name"], row["descriptor"]
    if key not in actual:
        raise ValueError("missing selected exact ABI")
    for field in ("flags", "code_present", "code_bytes", "code_sha256"):
        if row.get(field) != actual[key].get(field):
            raise ValueError("method " + field + " differs")


def check_archive(raw, provider, records, raw_classes):
    if len(raw) != provider["bytes"] or sha(raw) != provider["sha256"]:
        raise ValueError("provider archive byte pin differs")
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        names = archive.namelist()
        if len(names) != len(set(names)):
            raise ValueError("duplicate provider archive entry")
        notices = sorted(name for name in names if any(
            part in name.lower() for part in ("license", "notice", "copying")))
        if notices != provider["archive_license_notice_entries"]:
            raise ValueError("provider archive license inventory differs")
        count = 0
        for record in records:
            if record.get("provider_sha256") != provider["sha256"]:
                continue
            entry = record["provider_entry"]
            member = archive.read(entry)
            if member != raw_classes[entry.removesuffix(".class")]:
                raise ValueError("extracted class differs from provider archive")
            count += 1
        return count


def verify():
    manifest = json.loads((HERE / "manifest.json").read_bytes())
    classes, raw_classes = {}, {}
    seen_paths = set()
    for record in manifest["files"]:
        relative = Path(record["path"])
        if relative.is_absolute() or ".." in relative.parts or relative in seen_paths:
            raise ValueError("fixture path")
        seen_paths.add(relative)
        raw = (HERE / relative).read_bytes()
        if len(raw) != record["bytes"] or sha(raw) != record["sha256"]:
            raise ValueError("fixture byte pin differs: " + str(relative))
        if str(relative).endswith(".class"):
            owner, methods = class_methods(raw)
            if record["provider_entry"] != owner + ".class" or owner in classes:
                raise ValueError("class identity")
            classes[owner] = methods
            raw_classes[owner] = raw
    rows = json.loads((HERE / "methods.json").read_bytes())["methods"]
    seen = set()
    for row in rows:
        key = row["owner"], row["name"], row["descriptor"]
        if key in seen or sha(raw_classes[row["owner"]]) != row["class_sha256"]:
            raise ValueError("selected method identity")
        seen.add(key)
        check_method(row, classes[row["owner"]])
    archived_classes = 0
    local_archives = []
    for provider in manifest["providers"]:
        if "local_path" not in provider:
            continue
        relative = Path(provider["local_path"])
        if relative not in seen_paths:
            raise ValueError("unbound local provider archive")
        raw = (HERE / relative).read_bytes()
        archived_classes += check_archive(raw, provider, manifest["files"], raw_classes)
        local_archives.append((raw, provider))
    return classes, raw_classes, rows, manifest["files"], local_archives, archived_classes


def self_test(classes, raw_classes, rows, records, local_archives):
    import copy
    code = next(row for row in rows if row["code_present"])
    for field, bad in (("code_sha256", "0" * 64), ("descriptor", "(I)J")):
        wrong = copy.deepcopy(code)
        wrong[field] = bad
        try:
            check_method(wrong, classes[code["owner"]])
        except ValueError:
            pass
        else:
            raise AssertionError("forged method pin accepted")
    abstract = next(row for row in rows if not row["code_present"])
    wrong = dict(abstract, code_present=True, code_bytes=0, code_sha256=sha(b""))
    try:
        check_method(wrong, classes[abstract["owner"]])
    except ValueError:
        pass
    else:
        raise AssertionError("abstract method became empty body")
    try:
        class_methods(next(iter(raw_classes.values()))[:-1])
    except ValueError:
        pass
    else:
        raise AssertionError("truncated class accepted")
    for raw, provider in local_archives:
        try:
            check_archive(raw, dict(provider, sha256="0" * 64), records, raw_classes)
        except ValueError:
            pass
        else:
            raise AssertionError("forged archive pin accepted")
        selected = next(row for row in records
            if row.get("provider_sha256") == provider["sha256"])
        wrong_classes = dict(raw_classes)
        wrong_classes[selected["provider_entry"].removesuffix(".class")] = b"wrong class"
        try:
            check_archive(raw, provider, records, wrong_classes)
        except ValueError:
            pass
        else:
            raise AssertionError("extracted class/provider mismatch accepted")
    return 4 + 2 * len(local_archives)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    classes, raw, rows, records, archives, archived_classes = verify()
    controls = self_test(classes, raw, rows, records, archives) if args.self_test else 0
    print(json.dumps({"classes": len(classes), "selected_method_pins": len(rows),
        "local_provider_archives": len(archives), "archive_matched_classes": archived_classes,
        "adverse_controls": controls,
        "scope": "Byte/ABI/Code integrity only; no execution or omission authority"}))
