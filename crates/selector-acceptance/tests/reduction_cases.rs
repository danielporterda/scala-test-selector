//! Fast, compiler-backed change controls. Frozen JVM observations are evaluator
//! evidence only; no JVM, source compiler or legacy analyzer runs in this test.
use selector_solve::{AnalysisSeeds, SolveOptions, SolverRuntime, analyze_typed_with_runtime};
use selector_types::Completion;
use std::path::Path;
#[path = "support/reduction_fixture.rs"]
mod fixture;
use fixture::{root, snapshot};

#[test]
fn heldout_mutation_has_independent_jvm_receipt_and_only_the_other_helper_changes() {
    let base = root().join("fixtures/execution-smoke/base");
    let head = root().join("fixtures/reduction-heldout/head");
    let rows = |path: &Path| -> Vec<serde_json::Value> {
        std::fs::read_to_string(path.join("documents.jsonl"))
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect()
    };
    let before = rows(&base);
    let after = rows(&head);
    let changed: Vec<_> = after
        .iter()
        .filter(|new| {
            let old = before
                .iter()
                .find(|old| old["path"] == new["path"])
                .unwrap();
            old["source_sha256"] != new["source_sha256"]
        })
        .map(|row| row["path"].as_str().unwrap())
        .collect();
    assert_eq!(changed, ["src/executioncase/Unchanged.scala"]);
    for (directory, values) in [(&base, "observed:41,7,7"), (&head, "observed:41,9,9")] {
        let log = std::fs::read_to_string(directory.join("execution.log")).unwrap();
        assert_eq!(log.lines().next(), Some(values));
        assert_eq!(
            log.lines()
                .filter(|line| line.starts_with("suite:"))
                .count(),
            3
        );
        let runner = std::fs::read_to_string(directory.join("scalatest.log")).unwrap();
        assert!(runner.contains("Suites: completed 3, aborted 0"));
    }
}

#[test]
fn actual_mutations_reversion_and_unchanged_control_preserve_known_exclusions() {
    let expected: serde_json::Value = serde_json::from_slice(
        &std::fs::read(root().join("tools/dev-cases/execution-body-expected.json")).unwrap(),
    )
    .unwrap();
    let expected_required: Vec<_> = expected["required"]
        .as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap())
        .collect();
    let expected_unaffected: Vec<_> = expected["unaffected"]
        .as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap())
        .collect();
    let heldout_expected: serde_json::Value = serde_json::from_slice(
        &std::fs::read(root().join("tools/dev-cases/heldout-helper-expected.json")).unwrap(),
    )
    .unwrap();
    let heldout_required: Vec<_> = heldout_expected["required"]
        .as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap())
        .collect();
    let heldout_unaffected: Vec<_> = heldout_expected["unaffected"]
        .as_array()
        .unwrap()
        .iter()
        .map(|name| name.as_str().unwrap())
        .collect();
    for workers in [1, 4] {
        let directory = root().join("fixtures/execution-smoke");
        let base = snapshot(&directory.join("base"), workers);
        let head = snapshot(&directory.join("head"), workers);
        let heldout = snapshot(&root().join("fixtures/reduction-heldout/head"), workers);
        let options = SolveOptions {
            workers,
            memory_budget_bytes: 64 * 1024 * 1024,
            max_contexts: 10_000,
            max_steps: 1_000_000,
            ..Default::default()
        };
        let runtime = SolverRuntime::new(&options).unwrap();
        let no_required = Vec::new();
        for (label, old, new, path, required, unaffected) in [
            (
                "body mutation",
                &base,
                &head,
                "src/executioncase/Changed.scala",
                &expected_required,
                &expected_unaffected,
            ),
            (
                "reversion",
                &head,
                &base,
                "src/executioncase/Changed.scala",
                &expected_required,
                &expected_unaffected,
            ),
            (
                "unchanged admitted bytes",
                &head,
                &head,
                "src/executioncase/Changed.scala",
                &no_required,
                &expected_unaffected,
            ),
            (
                "held-out helper mutation",
                &base,
                &heldout,
                "src/executioncase/Unchanged.scala",
                &heldout_required,
                &heldout_unaffected,
            ),
        ] {
            let seeds =
                selector_select::changed_seeds(&old.0, &old.1, &new.0, &new.1, &[path]).unwrap();
            assert!(!seeds.conservative, "{label}");
            let before = analyze_typed_with_runtime(
                &old.0,
                &old.1,
                AnalysisSeeds {
                    execution: &seeds.base,
                    declarations: &seeds.base_compile,
                },
                &options,
                &runtime,
            )
            .unwrap();
            let after = analyze_typed_with_runtime(
                &new.0,
                &new.1,
                AnalysisSeeds {
                    execution: &seeds.head,
                    declarations: &seeds.head_compile,
                },
                &options,
                &runtime,
            )
            .unwrap();
            let result =
                selector_select::select(&old.0, &old.1, &new.0, &new.1, seeds, Some(before), after)
                    .unwrap();
            assert_eq!(result.completion, Completion::Complete, "{label}");
            assert!(result.obligations.is_empty(), "{label}");
            let selected: Vec<_> = result
                .suites
                .iter()
                .map(|suite| {
                    assert!(!suite.guarded, "{label}");
                    new.0.text(new.0.suites[suite.suite.index()].name)
                })
                .collect();
            assert_eq!(
                selected, *required,
                "{label}, {workers} workers: required suites must have impact proof"
            );
            for name in unaffected {
                assert!(
                    !selected.contains(name),
                    "{label}: unrelated {name} retained"
                );
            }
            assert_eq!(new.0.suites.len() - selected.len(), 3 - required.len());
        }
    }
}
