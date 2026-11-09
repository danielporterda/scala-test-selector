#!/usr/bin/env python3
"""Record locally available frozen workloads without running either analyzer."""
from __future__ import annotations

import ast
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess

REPO = Path(__file__).resolve().parents[3]
HERE = REPO / "ci-cost-study/rust-selector"


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as f:
        while block := f.read(1024 * 1024):
            h.update(block)
    return h.hexdigest()


def receipt(path):
    p = Path(path)
    if not p.is_absolute():
        p = REPO / p
    row = {"path": str(p.relative_to(REPO)) if p.is_relative_to(REPO) else str(p), "present": p.is_file()}
    if row["present"]:
        row.update(bytes=p.stat().st_size, sha256=digest(p))
    return row


def main():
    captures = []
    for revision in ["4d270fdbdd8619590ef5e520a78585f5bb1e304a", "c759ad48a1dffcbc4cc0abc6527a0252ced85f6b"]:
        capture = REPO / "ci-cost-study/compiler-selector/capture" / revision
        bundle = json.loads((capture / "replay-bundle.json").read_text())
        manifest = json.loads((capture / "documents-manifest.json").read_text())
        coverage = json.loads((capture / "source-coverage.json").read_text())
        inputs = [capture / name for name in ["replay-bundle.json", "documents-manifest.json", "source-coverage.json",
                  "semanticdb-documents.jsonl.gz", "compiler-contexts.json.gz", "ci-catalogue.json"]]
        inputs.extend(REPO / row["path"] for row in bundle["raw_layers"] + bundle["source_layers"])
        rows = [receipt(p) for p in dict.fromkeys(inputs)]
        for layer in bundle["raw_layers"] + bundle["source_layers"]:
            row = next(r for r in rows if r["path"] == layer["path"])
            assert row["sha256"] == layer["sha256"] and row["bytes"] == layer["bytes"]
        decoded = next(r for r in rows if r["path"].endswith("semanticdb-documents.jsonl.gz"))
        assert decoded["sha256"] == bundle["expected_decoded_jsonl_sha256"]
        captures.append({"revision": revision, "coverage": {k: coverage[k] for k in
            ["expected_compiled_scala_sources", "observed_scala_sources", "compiled_scala_without_semanticdb",
             "all_observed_sources_match_revision_or_generated_compiler_input", "counts"]},
            "manifest_counts": manifest["counts"], "producer": manifest["producer"],
            "unknown_schema_fields": manifest["unknown_schema_fields"], "errors": manifest["errors"],
            "inputs": rows, "qualification": "Compiler/source corpus is available; external binary bodies and a complete executable syntax corpus are separate requirements."})
    test_families = []
    for path in sorted((REPO / "ci-cost-study/compiler-selector").rglob("test_*.py")) + sorted((REPO / "ci-cost-study/helper-shadow").glob("test_*.py")):
        tree = ast.parse(path.read_bytes(), filename=str(path))
        tests = [node.name for node in ast.walk(tree) if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name.startswith("test_")]
        test_families.append({**receipt(path), "test_functions": len(tests)})
    old_inventory = json.loads((REPO / "ci-cost-study/helper-shadow/downstream-evaluation/v545-full-architecture-validation/input-inventory.json").read_text())
    original_pr7743 = [receipt(r["local_locator"]) for r in old_inventory["original_pr7743"]["missing_local_artifacts"]]
    output = {
        "schema": "rust-selector-input-inventory/v1", "observed_date": "2026-11-06",
        "inspected_source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip(),
        "host": {"platform": platform.platform(), "architecture": platform.machine(), "logical_cpus": os.cpu_count(),
            "physical_memory_bytes": os.sysconf("SC_PHYS_PAGES") * os.sysconf("SC_PAGE_SIZE"),
            "rustc": subprocess.check_output(["rustc", "--version"], text=True).strip(),
            "hardware_model": None, "hardware_model_qualification": "sysctl hardware-model query denied by sandbox; CPU count and RAM obtained from OS APIs."},
        "captures": captures,
        "pr7743_original_locations_currently_present": original_pr7743,
        "pr7743_rebuild_default_location_present": Path("/private/tmp/pr7743-rebuild-v552").exists(),
        "oracle_receipts": [receipt(p) for p in [
            "ci-cost-study/compiler-selector/evaluation/independent-baseline-pr7646.json",
            "ci-cost-study/helper-shadow/downstream-evaluation/v545-full-architecture-validation/complete-comparison.json",
            "ci-cost-study/helper-shadow/downstream-evaluation/pr7743-replay-v552/historical-baseline.json",
            "ci-cost-study/helper-shadow/downstream-evaluation/completed-import-installed-v623/README.md"]],
        "legacy_tests": {"files": len(test_families), "test_functions": sum(r["test_functions"] for r in test_families),
                         "execution_status": "inventoried_only_not_executed_by_this_script", "records": test_families},
        "numeric_acceptance_budgets": {"status": "not_yet_frozen", "full_run_latency_seconds": None,
            "peak_resident_bytes": None, "clean_build_seconds": None, "leaf_edit_rebuild_seconds": None,
            "qualification": "No new speedup or full rewrite acceptance is established by this inventory. Set measured budgets before performance claims; historical bounded prefixes are not full-run baselines."},
    }
    directory = HERE / "docs"
    directory.mkdir(exist_ok=True)
    (directory / "input-inventory.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"captures": len(captures), "legacy_test_files": len(test_families),
                      "legacy_test_functions": output["legacy_tests"]["test_functions"]}))


if __name__ == "__main__":
    main()
