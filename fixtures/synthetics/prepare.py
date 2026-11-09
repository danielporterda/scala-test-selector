#!/usr/bin/env python3
"""Extract genuine compiler rewrite examples; never executes the old selector."""
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
REVISION = "c759ad48a1dffcbc4cc0abc6527a0252ced85f6b"
SOURCE = REPO / "ci-cost-study/compiler-selector/capture" / REVISION / "semanticdb-documents.jsonl.gz"
EXPECTED_SHA = "4a1ebe630da1c27d45b08de11ed313c50bedc96959c6192f01b07679ab730d2b"
CLOCK = "canton/community/base/src/main/scala/com/digitalasset/canton/time/Clock.scala"
SPLICE = "apps/app/src/main/scala/org/lfdecentralizedtrust/splice/SpliceApp.scala"
CONFIG = "apps/app/src/main/scala/org/lfdecentralizedtrust/splice/config/ConfigTransforms.scala"
WANTED = {
    (CLOCK, 0): "selected_companion_apply",
    (CLOCK, 2): "typed_selected_apply",
    (CLOCK, 4): "callback_apply_selection",
    (CLOCK, 5): "enclosing_implicit_actual",
    (CLOCK, 6): "type_application_without_new_callee",
    (CLOCK, 7): "inserted_implicit_conversion",
    (SPLICE, 1): "nested_implicit_actual_calls",
}


def extract_text(text, span):
    lines = text.splitlines(keepends=True)
    before = sum(len(line.encode("utf-16-le")) for line in lines[:span["start_line"]]) + span["start_character"] * 2
    end = sum(len(line.encode("utf-16-le")) for line in lines[:span["end_line"]]) + span["end_character"] * 2
    return text.encode("utf-16-le")[before:end].decode("utf-16-le")


def main():
    assert hashlib.sha256(SOURCE.read_bytes()).hexdigest() == EXPECTED_SHA
    roots, nested, examples = Counter(), Counter(), {}
    total = 0
    with gzip.open(SOURCE, "rt") as reader:
        for line in reader:
            document = json.loads(line)
            for ordinal, synthetic in enumerate(document["document"].get("synthetics", [])):
                total += 1
                tree = synthetic.get("tree", {})
                roots.update(tree.keys())
                tags = set()
                pending = [tree]
                while pending:
                    value = pending.pop()
                    if isinstance(value, dict):
                        for key, child in value.items():
                            if key.endswith("_tree"):
                                nested[key] += 1
                                tags.add(key)
                            pending.append(child)
                    elif isinstance(value, list):
                        pending.extend(value)
                name = WANTED.get((document["path"], ordinal))
                if document["path"] == CONFIG:
                    for tag, label in [("function_tree", "deferred_synthetic_function"), ("macro_expansion_tree", "macro_expansion_without_runtime_body")]:
                        if tag in tags and label not in examples:
                            name = label
                            break
                if name:
                    examples[name] = {"id": name, "path": document["path"], "synthetic_ordinal": ordinal,
                        "revision": document["revision"], "source_sha256": document["source_sha256"],
                        "semanticdb_input_sha256": document["semanticdb_input_sha256"],
                        "source_excerpt": extract_text(document["source_text"], synthetic["range"]), "synthetic": synthetic}
    assert len(examples) == 9
    expected = {row["id"]: row for row in json.loads((HERE / "expected.json").read_text())["examples"]}
    assert set(expected) == set(examples)
    def callee(tree):
        while "apply_tree" in tree or "type_apply_tree" in tree:
            tree = tree.get("apply_tree", tree.get("type_apply_tree")).get("function", {})
        return tree.get("id_tree", {}).get("symbol") or tree.get("select_tree", {}).get("id", {}).get("symbol")
    for name, row in examples.items():
        assert callee(row["synthetic"]["tree"]) == expected[name]["inserted_callee"], name
        serialized = json.dumps(row["synthetic"], sort_keys=True)
        for key in ("compile_type_references", "inserted_argument_callees", "deferred_parameters"):
            for symbol in expected[name].get(key, []):
                assert json.dumps(symbol) in serialized, (name, symbol)
        if "compile_only_macro" in expected[name]:
            assert json.dumps(expected[name]["compile_only_macro"]) in serialized
    output = {"schema": "rust-selector-captured-synthetic-patterns/v1", "revision": REVISION,
        "source": str(SOURCE.relative_to(REPO)), "source_sha256": EXPECTED_SHA,
        "census": {"total": total, "root_tags": dict(sorted(roots.items())), "nested_tags": dict(sorted(nested.items()))},
        "examples": [examples[name] for name in sorted(examples)],
        "qualification": "Exact compiler tree values and exact UTF-16 source excerpts; independent classification assertions live in expected.json. No graph or runtime edges are generated here."}
    (HERE / "captured-patterns.json").write_text(json.dumps(output, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"total": total, "examples": len(examples), "root_tags": dict(roots)}))


if __name__ == "__main__":
    main()
