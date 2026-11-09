#!/usr/bin/env python3
"""Produce demand-only external Scala signatures for the native extractor.

The native requests/authority stages own source-context and ordered-provider
admission. JVM filename candidates below are SEARCH KEYS, never semantic IDs.
Only a unique, exact SCALA SymbolInformation identity can be published. Target
classpath views are immutable, class-only, hash-verified snapshots: no ambient
JDK, manifest Class-Path expansion, Java fallback, or broken-signature stubs.
"""
from __future__ import annotations

import argparse
import ctypes
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parents[1]
DOMAIN = "selector-demand-external-metadata/v1"
SETTINGS = {"stub_broken_signatures": False, "usejavacp": False,
            "include_jdk": False, "scala_library_synthetics": False,
            "classpath_view": "verified-class-only-no-manifest/v1"}
MAX_CLASS = 16 * 1024 * 1024


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""): h.update(chunk)
    return h.hexdigest()


def canonical(x) -> bytes:
    return json.dumps(x, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def read_json(path: Path, limit=256 * 1024 * 1024):
    op = gzip.open if path.suffix == ".gz" else open
    with op(path, "rb") as f: data = f.read(limit + 1)
    if len(data) > limit: raise ValueError(f"JSON input exceeds {limit} bytes: {path}")
    return json.loads(data)


def write_json(path: Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + f".tmp-{os.getpid()}")
    tmp.write_bytes(canonical(value) + b"\n"); os.replace(tmp, path)


def class_hash(path: Path, outer: str):
    name=outer+".class"
    if path.is_dir():
        member=path/name
        return sha(member) if member.is_file() else None
    with zipfile.ZipFile(path) as z:
        try: member=z.getinfo(name)
        except KeyError: return None
        if member.file_size>MAX_CLASS: raise ValueError("selected class bound exceeded")
        return hashlib.sha256(z.read(member)).hexdigest()


def command(argv, output: Path, name: str):
    """Measured native/JVM commands, without retaining unbounded stdout."""
    sys.path.insert(0, str(ROOT / "tools"))
    from runtime_acceptance import measure
    row = measure([str(a) for a in argv], output, name, cwd=ROOT)
    if row["exit_code"]:
        raise RuntimeError(f"{name} exited {row['exit_code']}; see {output}")
    return row


def owner_candidates(symbol: str) -> list[str]:
    """Exact lexical-owner search, supporting ordinary Scala2 ASCII names.

    A nested class's pickled owner may be its outermost class. Therefore every
    nominal prefix is searched; the converter must prove exact ID membership.
    Unsupported grammar is explicitly unsupported, not rewritten heuristically.
    """
    match = re.fullmatch(r"(.+?)([^/#.()]+|`[^`]+`)\((?:\+\d+)?\)\.", symbol)
    if not match: return []
    owner = match.group(1)
    tokens = re.findall(r"(`[^`]+`|[^/#.]+)([/#.])", owner)
    if "".join(a+b for a,b in tokens) != owner: return []
    package = ""; nominal = ""; result = []
    operators = dict(zip("~!=<>%&|^+-*/:#?@\\", ("$tilde", "$bang", "$eq", "$less", "$greater", "$percent", "$amp", "$bar", "$up", "$plus", "$minus", "$times", "$div", "$colon", "$hash", "$qmark", "$at", "$bslash")))
    def encoded(name):
        name = name[1:-1] if name.startswith("`") else name
        if not name or any(ord(c) > 127 for c in name): raise ValueError("unsupported JVM name")
        return "".join(operators.get(c, c) for c in name) if all(c.isalnum() or c in "_$" or c in operators for c in name) else None
    for name, kind in tokens:
        try: value = encoded(name)
        except ValueError: return []
        if not value: return []
        if kind == "/":
            if nominal: return []
            package += value + "/"
        else:
            nominal = nominal + "$" + value if nominal else value
            result.append(package + nominal)
            if kind == ".": result.append(package + nominal + "$")
    return list(dict.fromkeys(result))


def manifest_attributes(data: bytes) -> dict[str, str]:
    """Main section only, including the JAR continuation-line convention."""
    logical = []
    for raw in data.decode("utf-8", errors="strict").replace("\r\n", "\n").split("\n"):
        if not raw: break
        if raw.startswith(" "):
            if not logical: raise ValueError("orphan manifest continuation")
            logical[-1] += raw[1:]
        else: logical.append(raw)
    result = {}
    for line in logical:
        key, sep, value = line.partition(": ")
        if not sep or key.lower() in result: raise ValueError("malformed or duplicate manifest attribute")
        result[key.lower()] = value
    return result


def jar_classes(z: zipfile.ZipFile, feature: int) -> dict[str, zipfile.ZipInfo]:
    infos = z.infolist()
    if len(infos) > 250_000: raise ValueError("JAR member bound exceeded")
    names = [i.filename for i in infos]
    if len(set(names)) != len(names): raise ValueError("duplicate physical JAR member")
    attrs = manifest_attributes(z.read("META-INF/MANIFEST.MF")) if "META-INF/MANIFEST.MF" in names else {}
    if attrs.get("multi-release", "").lower() == "true" and feature == 0:
        raise ValueError("multi-release class view requires captured Java feature authority")
    mr = attrs.get("multi-release", "").lower() == "true" and feature >= 9
    selected = {}
    for info in infos:
        name = info.filename; version = 0
        if name.startswith("META-INF/versions/"):
            m = re.fullmatch(r"META-INF/versions/(\d+)/(.+)", name)
            if not mr or not m or not (9 <= int(m[1]) <= feature): continue
            version, name = int(m[1]), m[2]
        if not name.endswith(".class") or name.startswith("META-INF/"): continue
        if name.startswith("/") or ".." in name.split("/") or "\\" in name: raise ValueError("unsafe class path")
        if info.file_size > MAX_CLASS: raise ValueError("class byte bound exceeded")
        if name not in selected or selected[name][0] < version: selected[name] = (version, info)
    return {name: pair[1] for name, pair in selected.items()}


class Snapshots:
    """Content-addressed views shared by all contexts; no hardlink leases.

    APFS clonefile snapshots isolate later source mutation without copying the
    data extent. Materialized fallback/class-only ZIP bytes are charged before
    writing, including temporary files. A logical byte limit bounds clones too.
    """
    def __init__(self, cache: Path, disk_limit: int, logical_limit: int):
        self.cache = cache; cache.mkdir(parents=True, exist_ok=True)
        self.disk_limit = disk_limit; self.logical_limit = logical_limit
        self.materialized = 0; self.logical = 0; self.views = {}; self.receipts = []

    def reserve(self, size, materialized=True):
        if size < 0 or self.logical + size > self.logical_limit: raise ValueError("snapshot logical byte budget exceeded")
        if materialized and self.materialized + size > self.disk_limit: raise ValueError("snapshot materialized byte budget exceeded")
        self.logical += size
        if materialized: self.materialized += size

    def clone(self, source: Path, dest: Path, size: int):
        dest.parent.mkdir(parents=True, exist_ok=True)
        try:
            lib = ctypes.CDLL(None, use_errno=True)
            fn = lib.clonefile; fn.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_int]
            if fn(os.fsencode(source), os.fsencode(dest), 0) == 0:
                self.reserve(size, False); return "clonefile"
        except (AttributeError, OSError): pass
        self.reserve(size)
        with source.open("rb") as src, dest.open("xb") as dst:
            left = size
            while left:
                b = src.read(min(left, 1024*1024))
                if not b: raise ValueError("provider shrank during copy")
                dst.write(b); left -= len(b)
            if src.read(1): raise ValueError("provider grew during copy")
        return "copy"

    def get(self, entry: dict, original: dict, feature: int) -> Path:
        kind = entry["kind"]; expected = entry["sha256"]
        key = (kind, expected, feature)
        if key in self.views: return self.views[key]
        if kind == "unavailable": raise ValueError("unavailable classpath input cannot form complete metadata index")
        final = self.cache / f"{kind}-{expected}-java{feature}"
        metadata = final / "view.json"
        if metadata.exists():
            saved = read_json(metadata)
            if saved.get("source_sha256") != expected or saved.get("feature") != feature: raise ValueError("snapshot cache identity mismatch")
            # An externally mutable cache is not authority. Rebind every member
            # to freshly verified original bytes once/process before reuse.
            source=Path(entry["physical_path"]); expected_records=[]
            if kind == "jar":
                if sha(source)!=expected: raise ValueError("cached original JAR changed")
                with zipfile.ZipFile(source) as z:
                    for name,info in sorted(jar_classes(z,feature).items()):
                        data=z.read(info); expected_records.append({"path":name,"bytes":len(data),"sha256":hashlib.sha256(data).hexdigest()})
                with zipfile.ZipFile(final/"classes.jar") as z:
                    if sorted(z.namelist())!=[r["path"] for r in expected_records]: raise ValueError("unexpected manifest/resource in immutable class view")
                    actual=[]
                    for name,info in sorted(jar_classes(z,feature).items()):
                        data=z.read(info); actual.append({"path":name,"bytes":len(data),"sha256":hashlib.sha256(data).hexdigest()})
                if actual!=expected_records: raise ValueError("cached derived JAR differs from admitted original")
            else:
                inventory=[]
                for p in sorted(source.rglob("*")) if kind=="directory" else []:
                    if p.is_symlink(): raise ValueError("symlink in cached original")
                    if p.is_file(): inventory.append({"path":p.relative_to(source).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)})
                inventory.sort(key=lambda r:r["path"])
                if kind=="directory" and hashlib.sha256(canonical(inventory)).hexdigest()!=expected: raise ValueError("cached original directory changed")
                expected_records=[r for r in inventory if r["path"].endswith(".class")]
                actual=[]
                for p in sorted((final/"classes").rglob("*")):
                    if p.is_symlink(): raise ValueError("symlink in class view")
                    if p.is_file(): actual.append({"path":p.relative_to(final/"classes").as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)})
                actual.sort(key=lambda r:r["path"])
                if actual!=expected_records: raise ValueError("cached directory view differs from admitted original")
            if sorted(saved["classes"],key=lambda r:r["path"])!=expected_records: raise ValueError("snapshot manifest mutation")
            self.reserve(saved["class_bytes"], False)
            self.views[key] = final / ("classes.jar" if kind == "jar" else "classes"); self.receipts.append(saved); return self.views[key]
        temp = Path(tempfile.mkdtemp(prefix="building-", dir=self.cache)); classes = temp / "classes"; classes.mkdir()
        records = []; source = Path(entry["physical_path"])
        try:
            if kind == "jar":
                # Clone the whole original archive, verify independently, then
                # project classes without manifest expansion or MR ambiguity.
                size = source.stat().st_size
                archive = temp / "source.jar"
                mode = self.clone(source, archive, size)
                if sha(archive) != expected: raise ValueError("JAR provider mutation or hash mismatch")
                with zipfile.ZipFile(archive) as z, zipfile.ZipFile(temp/"classes.jar", "w", compression=zipfile.ZIP_DEFLATED) as target:
                    charged = 0
                    for name, info in sorted(jar_classes(z, feature).items()):
                        self.reserve(info.file_size, False)
                        # A single class is bounded by16MiB; reserve its worst
                        # compressed size before writing, then charge actuals.
                        if self.materialized + info.file_size + 65536 > self.disk_limit: raise ValueError("snapshot materialized byte budget exceeded")
                        data = z.read(info)
                        member = zipfile.ZipInfo(name, date_time=(1980,1,1,0,0,0)); member.compress_type=zipfile.ZIP_DEFLATED
                        target.writestr(member,data)
                        size_now = target.fp.tell(); self.materialized += size_now-charged; charged=size_now
                        records.append({"path": name, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()})
                    # Central directory is bounded by membercount and names.
                    overhead=sum(46+len(r["path"].encode()) for r in records)+22
                    if self.materialized+overhead > self.disk_limit: raise ValueError("snapshot central directory byte budget exceeded")
                    self.materialized+=overhead
                archive.unlink()
            elif kind == "directory":
                inventory = []; mode = "class-clones"
                # Hash the COMPLETE captured directory inventory. Metadata and
                # nonclass files are part of source admission, not class lookup.
                for base, dirs, files in os.walk(source, followlinks=False):
                    dirs.sort(); files.sort()
                    if any((Path(base)/d).is_symlink() for d in dirs): raise ValueError("symlink in provider directory")
                    for name in files:
                        p = Path(base)/name; st = p.lstat()
                        if not stat.S_ISREG(st.st_mode): raise ValueError("nonregular provider member")
                        rel = p.relative_to(source).as_posix(); digest = sha(p)
                        inventory.append({"path": rel, "bytes": st.st_size, "sha256": digest})
                        if len(inventory) > 250_000: raise ValueError("directory member budget exceeded")
                        if rel.endswith(".class"):
                            if st.st_size > MAX_CLASS: raise ValueError("class size bound exceeded")
                            dest = classes / rel; self.clone(p, dest, st.st_size)
                            if sha(dest) != digest: raise ValueError("class changed during immutable snapshot")
                            records.append(inventory[-1])
                inventory.sort(key=lambda r: r["path"])
                if hashlib.sha256(canonical(inventory)).hexdigest() != expected: raise ValueError("complete provider directory hash mismatch")
                if original.get("files") is not None and original["files"] != len(inventory): raise ValueError("directory file count mismatch")
                if original.get("bytes") is not None and original["bytes"] != sum(r["bytes"] for r in inventory): raise ValueError("directory byte count mismatch")
            elif kind == "absent_empty_output":
                mode = "admitted-empty"
            else: raise ValueError(f"unsupported provider kind: {kind}")
            records.sort(key=lambda r:r["path"])
            saved = {"schema": "selector-metadata-class-view/v1", "source_sha256": expected,
                     "source_kind": kind, "feature": feature, "snapshot_mode": mode,
                     "class_bytes": sum(r["bytes"] for r in records), "classes": records}
            if kind == "jar": saved["view_sha256"] = sha(temp/"classes.jar")
            write_json(temp / "view.json", saved)
            try: os.rename(temp, final)
            except FileExistsError: shutil.rmtree(temp)
            self.views[key] = final / ("classes.jar" if kind == "jar" else "classes"); self.receipts.append(saved); return self.views[key]
        except BaseException:
            shutil.rmtree(temp, ignore_errors=True); raise


def helper(output: Path, java: Path, receipts: list, cache_root: Path | None=None) -> tuple[Path, list[Path], str]:
    manifest = read_json(ROOT / "fixtures/selected-external-apply/manifest.json")
    jars = [Path(r["path"]) for r in manifest["jars"]]
    for row, path in zip(manifest["jars"], jars):
        if sha(path) != row["sha256"]: raise ValueError(f"toolchain hash mismatch: {path}")
    sources = [ROOT / "tools/metadata/DemandConverter.java", ROOT / "tools/metadata/ExternalMetadataBatch.scala"]
    tool = {"domain": DOMAIN, "sources": {p.name: sha(p) for p in sources},
            "driver_sha256": sha(Path(__file__)), "jars": [{"name": p.name, "sha256": sha(p)} for p in jars],
            "java_sha256": sha(java), "settings": SETTINGS}
    identity = hashlib.sha256(canonical(tool)).hexdigest()
    # Driver changes invalidate produced metadata, but not an unchanged JVM
    # helper binary. Share its compilation across contexts, sides and outputs.
    compile_key=hashlib.sha256(canonical({k:v for k,v in tool.items() if k!="driver_sha256"})).hexdigest()
    cache = (cache_root or output/"helper-cache") / compile_key; jar = cache / "metadata-helper.jar"
    if not jar.exists():
        classes = cache / "classes"; classes.mkdir(parents=True, exist_ok=True)
        cp = os.pathsep.join(str(p) for p in jars)
        receipts.append(command([java.with_name("javac"), "-cp", cp, "-d", classes, sources[0]], output, "compile-java-bridge"))
        receipts.append(command([java, "-Xmx512m", "-cp", os.pathsep.join(str(p) for p in jars[:3]),
            "scala.tools.nsc.Main", "-classpath", str(classes)+os.pathsep+cp, "-d", classes, sources[1]], output, "compile-scala-helper"))
        with zipfile.ZipFile(jar, "w", compression=zipfile.ZIP_DEFLATED) as z:
            for p in sorted(classes.rglob("*.class")):
                i = zipfile.ZipInfo(p.relative_to(classes).as_posix(), date_time=(1980,1,1,0,0,0)); i.compress_type = zipfile.ZIP_DEFLATED
                z.writestr(i, p.read_bytes())
        write_json(cache / "producer.json", tool | {"producer_sha256": identity, "helper_sha256": sha(jar)})
    else:
        saved = read_json(cache / "producer.json")
        if sha(jar) != saved["helper_sha256"]: raise ValueError("compiled helper cache mutation")
    write_json(output/"producer.json",tool | {"producer_sha256":identity,
        "helper_path":str(jar),"helper_sha256":sha(jar),"compilation_cache_key":compile_key})
    return jar, jars, identity


def produce(args):
    output = args.output_dir.resolve(); output.mkdir(parents=True, exist_ok=True)
    started = time.time(); commands = []; failures = []; driver_start=sha(Path(__file__))
    requests = read_json(args.requests); contexts = read_json(args.contexts)
    if requests["schema"] != "compiler-external-metadata-requests/v1": raise ValueError("wrong request schema")
    if sha(args.contexts) != requests["contexts_sha256"]: raise ValueError("requests/context physical hash mismatch")
    exact = set(args.symbol or [])
    if args.symbols_file: exact.update(s for s in args.symbols_file.read_text().splitlines() if s)
    if not exact and not args.all_demands: raise ValueError("use exact --symbol/--symbols-file filters or explicit --all-demands")
    chosen = [r for r in requests["requests"] if (not exact or r["symbol"] in exact) and (not args.context or r["context"] in args.context)]
    missing = exact - {r["symbol"] for r in chosen}
    if missing: raise ValueError("exact requested roots absent from plan: " + repr(sorted(missing)))
    if len(chosen) > args.max_requests: raise ValueError("selected request limit exceeded")
    by_context = {c["context_id"]: c for c in contexts["contexts"]}
    search = {}; candidate_requests = set()
    for row in chosen:
        key = (row["context"], row["symbol"]); candidates = owner_candidates(row["symbol"]); search[key] = candidates
        if not candidates: failures.append(row | {"reason": "unsupported_owner_grammar"})
        for context in row["context"].split("\0"):
            if context not in by_context: raise ValueError("request context absent from capture")
            candidate_requests.update((context, candidate) for candidate in candidates)
    provider_requests = output / "provider-requests.json"
    write_json(provider_requests, {"schema":"external-metadata-provider-requests/v1", "classes":[{"context":c,"outer_class":o} for c,o in sorted(candidate_requests)]})
    authority_path = output / "authority.json"
    commands.append(command([args.selector, "metadata-authority", "--contexts", args.contexts,
        "--metadata-binary-map", args.metadata_binary_map, "--compiler-input-root", args.compiler_input_root,
        "--input", provider_requests, "--output", authority_path], output, "native-authority"))
    authority = read_json(authority_path)
    if authority["contexts_sha256"] != requests["contexts_sha256"] or authority["requests_sha256"] != sha(provider_requests): raise ValueError("native authority receipt mismatch")
    proofs = {(r["context"],r["outer_class"]):r for r in authority["classes"]}
    physical = {r["captured_path"]:r for r in authority["physical_authority"]["entries"]}
    objects = {r["path"]:r for r in contexts.get("input_objects", [])}
    captured_java = contexts.get("java_runtime",{}).get("java_version")
    # Unknown Java authority is retained as0. Ordinary archives have the same
    # class view on every JVM; MR archives reject this sentinel above.
    feature = int(re.match(r"(?:1\.)?(\d+)", captured_java)[1]) if captured_java else 0
    if args.java_feature is not None and feature != args.java_feature: raise ValueError("Java feature disagrees with capture")
    snapshots = Snapshots(args.snapshot_cache.resolve(), args.max_snapshot_bytes, args.max_snapshot_logical_bytes)
    jar, jars, producer = helper(output, args.java.resolve(), commands, args.snapshot_cache.resolve().parent/"external-metadata-helper-cache")
    grouped = {}
    for key,candidates in search.items():
        full_context, root = key
        for context in full_context.split("\0"):
            for outer in candidates:
                proof = proofs[(context,outer)]
                if not proof["available"]: continue
                env = by_context[context].get("compiler_environment_fingerprint", "")
                group = (proof["classpath_sha256"],env)
                g = grouped.setdefault(group, {"contexts":set(),"tasks":{}})
                g["contexts"].add(context)
                g["tasks"].setdefault((outer,proof["class_sha256"]),set()).add(root)
    results = {}; payloads = []; payload_index = {}; executed_batches=0
    for ordinal, (group,g) in enumerate(sorted(grouped.items())):
        groupdir = output / f"batch-{ordinal:04d}"; groupdir.mkdir(exist_ok=True)
        representative = sorted(g["contexts"])[0]; ctx = by_context[representative]
        paths = []
        try:
            for item in ctx["full_classpath"]:
                captured = item.get("input_object") or item["path"]
                entry = physical[captured]
                if item.get("sha256") != entry["sha256"]: raise ValueError("ordered context provider differs from authority")
                paths.append(snapshots.get(entry,objects.get(captured,{}),feature))
        except Exception as e:
            failures.append({"contexts":sorted(g["contexts"]),"reason":"incomplete_immutable_classpath", "detail":str(e)[:2048]}); continue
        cpfile = groupdir / "classpath.txt"; cpfile.write_text("".join(str(p)+"\n" for p in paths))
        tasks = sorted(g["tasks"])
        taskfile = groupdir / "requests.tsv"
        taskfile.write_text("".join("\t".join([outer,digest,*sorted(g["tasks"][(outer,digest)])])+"\n" for outer,digest in tasks))
        # Verify the derived immutable class view's first selected provider is
        # exactly the native lookup result, not merely a same-named class.
        for context in sorted(g["contexts"]):
            for outer,digest in tasks:
                proof = proofs.get((context,outer))
                if not proof or not proof["available"]: continue
                found = next(((i,h) for i,p in enumerate(paths) if (h:=class_hash(p,outer)) is not None),None)
                if found is None or found[0] != proof["provider_index"] or found[1] != digest: raise ValueError("immutable index disagrees with admitted selected provider")
        commands.append(command([args.java, f"-Xmx{args.heap_mib}m", "-cp", os.pathsep.join(str(p) for p in [jar,*jars]),
            "ExternalMetadataBatch", cpfile, taskfile, groupdir], output, f"metadata-batch-{ordinal:04d}"))
        executed_batches+=1
        batch = read_json(groupdir / "result.json")
        for cls in batch["classes"]:
            payload = cls["payload"]
            if payload:
                p = groupdir / payload; digest = sha(p)
                if digest not in payload_index:
                    payload_index[digest] = len(payloads); payloads.append({"path":str(p.relative_to(output)),"sha256":digest})
                pidx = payload_index[digest]
            else: pidx = None
            for context in g["contexts"]:
                for method in cls["methods"]:
                    if method["success"]:
                        results.setdefault((context,method["symbol"]),[]).append((cls["outer_class"],pidx,method["semantic_sha256"]))
                    else: failures.append({"context":context,"outer_class":cls["outer_class"],**method})
            if cls["error"]: failures.append({"contexts":sorted(g["contexts"]),"outer_class":cls["outer_class"],"reason":"unsupported_class", "detail":cls["error"]})
    bindings = []
    for row in chosen:
        projections = []; hashes = []; bad = None
        for context in row["context"].split("\0"):
            found = results.get((context,row["symbol"]),[])
            if len(found) != 1:
                bad = "exact_root_absent" if not found else "ambiguous_scala_signature_owners"; break
            outer,pidx,semantic_hash = found[0]; proof = proofs[(context,outer)]
            projections.append({"context":context,"payload":pidx,"outer_class":outer,
                "outer_class_sha256":proof["class_sha256"],"classpath_sha256":proof["classpath_sha256"],
                "provider_index":proof["provider_index"],"provider_sha256":proof["provider_sha256"]})
            hashes.append(semantic_hash)
        if bad or len(set(hashes)) != 1:
            failures.append(row | {"reason":bad or "composite_context_signature_conflict"}); continue
        bindings.append({"context":row["context"],"roots":[row["symbol"]],"projections":projections})
    manifest = {"schema":"compiler-external-metadata/v1", "producer_sha256":producer,
        "authority_sha256":authority["authority_sha256"],"contexts_sha256":requests["contexts_sha256"],
        "payloads":payloads,"bindings":bindings}
    if sha(Path(__file__))!=driver_start: raise ValueError("producer source changed during publication; rerun stable source")
    write_json(output / "manifest.json",manifest)
    # Full class inventories stay in the shared cache; compact receipt pins them.
    receipt = {"schema":DOMAIN,"producer_sha256":producer,"requests_path":str(args.requests.resolve()),
        "requests_sha256":sha(args.requests),"request_identity":requests["request_identity"],
        "contexts_path":str(args.contexts.resolve()),"contexts_sha256":sha(args.contexts),
        "binary_map_sha256":sha(args.metadata_binary_map),"authority_sha256":sha(authority_path),
        "selected_requests":len(chosen),"admitted_requests":len(bindings),"payloads":len(payloads),
        "selector_sha256":sha(args.selector),"producer_inputs_sha256":sha(output/"producer.json"),
        "jvm_batches":executed_batches,"planned_classpath_batches":len(grouped),"failures":failures,"commands":commands,
        "snapshot_materialized_bytes":snapshots.materialized,"snapshot_logical_bytes":snapshots.logical,
        "views":[{"source_sha256":r["source_sha256"],"source_kind":r["source_kind"],"feature":r["feature"],
                  "class_bytes":r["class_bytes"],"classes":len(r["classes"])} for r in snapshots.receipts],
        "manifest_sha256":sha(output/"manifest.json"),"wall_seconds":time.time()-started,
        "scope":"signature metadata only; omitted/unsupported requests retain native analysis guards"}
    write_json(output / "receipt.json",receipt)
    print(json.dumps({k:receipt[k] for k in ("selected_requests","admitted_requests","payloads","jvm_batches","snapshot_materialized_bytes","snapshot_logical_bytes","wall_seconds")}))
    print("manifest="+str(output/"manifest.json")); print("producer_sha256="+producer)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--selector",type=Path,required=True); p.add_argument("--requests",type=Path,required=True)
    p.add_argument("--contexts",type=Path,required=True); p.add_argument("--metadata-binary-map",type=Path,required=True)
    p.add_argument("--compiler-input-root",type=Path,required=True); p.add_argument("--output-dir",type=Path,required=True)
    p.add_argument("--symbol",action="append"); p.add_argument("--symbols-file",type=Path)
    p.add_argument("--context",action="append"); p.add_argument("--all-demands",action="store_true")
    p.add_argument("--max-requests",type=int,default=4096)
    p.add_argument("--snapshot-cache",type=Path,default=ROOT/"artifacts/external-metadata-class-views")
    p.add_argument("--max-snapshot-bytes",type=int,default=500*1024*1024)
    p.add_argument("--max-snapshot-logical-bytes",type=int,default=4*1024*1024*1024)
    p.add_argument("--heap-mib",type=int,default=512)
    p.add_argument("--java-feature",type=int,help="assert an already captured Java feature; never supplies missing authority")
    p.add_argument("--java",type=Path,default=Path("/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home/bin/java"))
    args=p.parse_args()
    if not 128 <= args.heap_mib <= 1024: p.error("heap must be128..1024MiB")
    if args.max_requests <= 0 or args.max_requests > 200_000: p.error("max-requests must be1..200000")
    produce(args)


if __name__ == "__main__": main()
