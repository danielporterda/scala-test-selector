#!/usr/bin/env python3
"""Development-only extraction of immutable, genuine compiler fixture inputs.

Rust tests consume the checked-in outputs directly; this script is never called
by Cargo, the selector, or build.rs. No compiler or previous analyzer executes.
"""
from __future__ import annotations

import argparse
import base64
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import tarfile


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
REVISION = "c759ad48a1dffcbc4cc0abc6527a0252ced85f6b"
CAPTURE = REPO / "ci-cost-study/compiler-selector/capture" / REVISION
ORIGINAL_AST = REPO / "ci-cost-study/helper-shadow/downstream-evaluation/annotation-lexical-v403/captured-fixture.json.gz"
PATHS = (
    "apps/app/src/main/scala/org/lfdecentralizedtrust/splice/SpliceApp.scala",
    "canton/community/base/src/main/scala/com/digitalasset/canton/time/Clock.scala",
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def encode(value) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode()


def receipt(path: Path) -> dict:
    data = path.read_bytes()
    return {"path": str(path.relative_to(REPO)), "bytes": len(data), "sha256": sha(data)}


def range_text(text: str, span: dict) -> str:
    """SemanticDB columns are UTF-16 units, not UTF-8 bytes or Python indexes."""
    lines = text.splitlines(keepends=True)
    start, end = span["start_line"], span["end_line"]
    if start == end:
        raw = lines[start].encode("utf-16-le")
        return raw[span["start_character"] * 2:span["end_character"] * 2].decode("utf-16-le")
    return (lines[start].encode("utf-16-le")[span["start_character"] * 2:].decode("utf-16-le")
            + "".join(lines[start + 1:end])
            + lines[end].encode("utf-16-le")[:span["end_character"] * 2].decode("utf-16-le"))


def prepare(native_syntax: Path | None = None, native_tooling: Path | None = None) -> None:
    target = HERE / "compiler-smoke"
    target.mkdir(parents=True, exist_ok=True)
    bundle_path = CAPTURE / "replay-bundle.json"
    bundle = json.loads(bundle_path.read_bytes())
    manifest_path = REPO / bundle["documents_manifest"]["path"]
    assert sha(manifest_path.read_bytes()) == bundle["documents_manifest"]["sha256"]
    manifest = json.loads(manifest_path.read_bytes())
    records = {r["path"]: r for r in manifest["documents"] if r["path"] in PATHS}
    assert set(records) == set(PATHS)
    selected, original_lines = {}, {}
    decoded_path = CAPTURE / "semanticdb-documents.jsonl.gz"
    assert sha(decoded_path.read_bytes()) == bundle["expected_decoded_jsonl_sha256"]
    with gzip.open(decoded_path, "rb") as reader:
        for line in reader:
            row = json.loads(line)
            if row["path"] in PATHS:
                assert row["path"] not in selected
                selected[row["path"]] = row
                original_lines[row["path"]] = line
    assert set(selected) == set(PATHS)
    ast_fixture = json.loads(gzip.decompress(ORIGINAL_AST.read_bytes()))
    ast_records = {r["path"]: r for r in ast_fixture["documents"]}
    syntax_rows, provenance = [], []
    for index, path in enumerate(PATHS):
        row, record = selected[path], records[path]
        source = row["source_text"].encode()
        assert row["revision"] == REVISION
        assert row["source_sha256"] == sha(source) == record["source_sha256"]
        assert row["source_md5_matches"] is True
        assert hashlib.md5(source).hexdigest().lower() == row["document"]["md5"].lower()
        (target / ("splice-app.scala" if index == 0 else "clock.scala")).write_bytes(source)
        syntax_status = "native_scalaspans_source_hash_bound"
        if path in ast_records:
            ast = ast_records[path]
            assert base64.b64decode(ast["source_base64"], validate=True) == source
            assert ast["ast"]["sha256"] == sha(source)
            for field in ("symbols", "occurrences", "synthetics"):
                assert Counter(encode(v) for v in ast["document"][field]) == Counter(encode(v) for v in row["document"][field])
            syntax_rows.append({"path": path, "source_sha256": sha(source),
                "producer_sha256": ast_fixture["scope"]["syntax_producer"], "ast": ast["ast"]})
        provenance.append({**record, "syntax_status": syntax_status,
            "symbols": len(row["document"].get("symbols", [])),
            "occurrences": len(row["document"].get("occurrences", [])),
            "synthetics": len(row["document"].get("synthetics", []))})
    (target / "documents.jsonl").write_bytes(b"".join(original_lines[p] for p in PATHS))
    (target / "helper-syntax.jsonl").write_bytes(b"".join(encode(row) for row in syntax_rows))
    if native_syntax is not None:
        assert native_tooling is not None, "native producer tooling receipt is required"
        tooling = json.loads(native_tooling.read_bytes())
        assert sha(Path(tooling["exporter"]).read_bytes()) == tooling["exporter_sha256"]
        for jar in tooling["jars"]:
            assert sha(Path(jar["path"]).read_bytes()) == jar["sha256"]
        native = [json.loads(line) for line in native_syntax.read_bytes().splitlines()]
        assert {row["path"] for row in native} == set(PATHS)
        for row in native:
            assert row["source_sha256"] == selected[row["path"]]["source_sha256"] == row["ast"]["sha256"]
            assert row["producer_sha256"] == tooling["exporter_sha256"]
            assert "members" in row["ast"] and "owners" in row["ast"]
        (target / "syntax.jsonl").write_bytes(native_syntax.read_bytes())
        (target / "native-tooling.json").write_bytes(native_tooling.read_bytes())
    assert (target / "syntax.jsonl").is_file(), "supply actual --native-syntax and --native-tooling outputs on first preparation"
    tooling = json.loads((target / "native-tooling.json").read_bytes())
    wanted = {record["semanticdb_input_sha256"] for record in records.values()}
    recovered = set()
    raw_dir = target / "raw"
    raw_dir.mkdir(exist_ok=True)
    for layer in bundle["raw_layers"]:
        archive_path = REPO / layer["path"]
        assert sha(archive_path.read_bytes()) == layer["sha256"]
        with tarfile.open(archive_path, "r:gz") as archive:
            for member in archive:
                if not member.isfile():
                    continue
                if member.name not in {r["semanticdb_input"] for r in records.values()} and Path(member.name).stem not in wanted:
                    continue
                raw = archive.extractfile(member).read()
                digest = sha(raw)
                if digest in wanted:
                    (raw_dir / (digest + ".semanticdb")).write_bytes(raw)
                    recovered.add(digest)
    assert recovered == wanted
    output_paths = sorted(p for p in target.rglob("*") if p.is_file() and p.name not in ("manifest.json", "expected.json"))
    fixture_manifest = {
        "schema": "rust-selector-compiler-fixture/v1", "revision": REVISION,
        "kind": "exact_subset_of_real_capture", "new_compilation": False,
        "producer": manifest["producer"], "upstream_bundle": receipt(bundle_path),
        "upstream_manifest": receipt(manifest_path), "upstream_decoded": receipt(decoded_path),
        "upstream_syntax": receipt(ORIGINAL_AST), "raw_layers": bundle["raw_layers"],
        "native_syntax": {"producer_sha256": tooling["exporter_sha256"],
            "producer_identity_scope": "exporter source digest; ordered JVM classpath hashes retained separately in native-tooling.json",
            "producer": "actual ScalaSpans JVM run over the exact two captured source texts", "new_product_compilation": False},
        "records": provenance, "outputs": [receipt(p) for p in output_paths],
        "limitations": [
            "Two source/compiler documents are not a closed program or a complete suite catalogue.",
            "Native ScalaSpans syntax is newly produced from the exact two captured source texts; it is not a historical PR7646 syntax artifact.",
            "The separately retained helper-syntax.jsonl Clock lowering has identical source bytes and compiler record multisets, but its occurrence order and raw protobuf hashes differ; original PR7646 document order is preserved.",
            "No external binary bodies or successful runtime-provider results are fabricated.",
            "Expected direct body calls are source-reviewed acceptance assertions, not earlier selector output.",
        ],
    }
    (target / "manifest.json").write_bytes(json.dumps(fixture_manifest, indent=2).encode() + b"\n")
    verify()


def verify() -> None:
    target = HERE / "compiler-smoke"
    manifest = json.loads((target / "manifest.json").read_bytes())
    for output in manifest["outputs"]:
        path = REPO / output["path"]
        assert receipt(path) == output, path
    rows = [json.loads(line) for line in (target / "documents.jsonl").read_bytes().splitlines()]
    syntax = {r["path"]: r for r in map(json.loads, (target / "syntax.jsonl").read_bytes().splitlines())}
    helper_syntax = {r["path"]: r for r in map(json.loads, (target / "helper-syntax.jsonl").read_bytes().splitlines())}
    by_path = {r["path"]: r for r in rows}
    for row in rows:
        data = row["source_text"].encode()
        assert sha(data) == row["source_sha256"]
        assert hashlib.md5(data).hexdigest().lower() == row["document"]["md5"].lower()
        assert syntax[row["path"]]["source_sha256"] == syntax[row["path"]]["ast"]["sha256"] == row["source_sha256"]
    expected_path = target / "expected.json"
    if expected_path.exists():
        expected = json.loads(expected_path.read_bytes())
        for record in expected["declarations"]:
            row = by_path[record["path"]]
            info = next(i for i in row["document"]["symbols"] if i["symbol"] == record["symbol"])
            assert info["kind"] == record["kind"]
            assert info.get("overridden_symbols", []) == record.get("overridden_symbols", [])
        for call in expected["body_calls"]:
            row = by_path[call["path"]]
            assert range_text(row["source_text"], call["body_range"]) == call["body_source"]
            owner_defs = [o for o in row["document"]["occurrences"]
                          if o["symbol"] == call["from_symbol"] and o["role"] == 2]
            assert len(owner_defs) == 1
            assert any(m["definition_range"] == owner_defs[0]["range"] and m["body_range"] == call["body_range"]
                       for m in helper_syntax[call["path"]]["ast"]["methods"])
            def utf16_position(span, end=False):
                prefix = "end" if end else "start"
                lines = row["source_text"].splitlines(keepends=True)
                return sum(len(line.encode("utf-16-le")) // 2 for line in lines[:span[prefix + "_line"]]) + span[prefix + "_character"]
            definition = owner_defs[0]["range"]
            assert any(m["name_start"] == utf16_position(definition)
                       and m["name_end"] == utf16_position(definition, True)
                       and m["body_start"] == utf16_position(call["body_range"])
                       and m["body_end"] == utf16_position(call["body_range"], True)
                       for m in syntax[call["path"]]["ast"]["members"])
            assert any(o["symbol"] == call["to_symbol"] and o["role"] == 1 and o["range"] == call["reference_range"]
                       for o in row["document"]["occurrences"])
            assert range_text(row["source_text"], call["reference_range"]) == "internalMonotonicTime"
    print(json.dumps({"verified": True, "documents": len(rows), "syntax_documents": len(syntax),
                      "bytes": sum(r["bytes"] for r in manifest["outputs"])}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="verify checked-in outputs without original large inputs")
    parser.add_argument("--native-syntax", type=Path, help="actual ScalaSpans JVM JSONL output")
    parser.add_argument("--native-tooling", type=Path, help="ordered, hash-bound JVM tooling receipt")
    args = parser.parse_args()
    verify() if args.verify else prepare(args.native_syntax, args.native_tooling)
