//! Read-only paired classpath proof, without building an execution graph.
use selector_runtime_equivalence::{self as runtime_equivalence, BuildStampPolicy, Inputs};
use std::path::Path;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let arguments: Vec<_> = std::env::args_os().skip(1).collect();
    if let [mode, base, head, repo] = arguments.as_slice()
        && mode == "preflight-tracked-test"
    {
        let changes = runtime_equivalence::preflight_tracked_test_delta(
            Path::new(repo),
            base.to_str().ok_or("invalid base revision")?,
            head.to_str().ok_or("invalid head revision")?,
        )?;
        serde_json::to_writer_pretty(std::io::stdout().lock(), &changes)?;
        println!();
        return Ok(());
    }
    let [
        mode,
        base_contexts,
        base_catalogue,
        base_root,
        head_contexts,
        head_catalogue,
        head_root,
        tail @ ..,
    ] = arguments.as_slice()
    else {
        return Err("usage: runtime_equivalence preflight-tracked-test BASE_SHA HEAD_SHA GIT_REPO | compare BASE_CONTEXTS BASE_CATALOGUE BASE_ROOT HEAD_CONTEXTS HEAD_CATALOGUE HEAD_ROOT [--assume-unchanged-build-stamp] | audit-test-classpath-delta BASE_CONTEXTS BASE_CATALOGUE BASE_ROOT HEAD_CONTEXTS HEAD_CATALOGUE HEAD_ROOT CONTEXT_ID | select-tracked-test BASE_CONTEXTS BASE_CATALOGUE BASE_ROOT HEAD_CONTEXTS HEAD_CATALOGUE HEAD_ROOT GIT_REPO [--assume-unchanged-build-stamp]".into());
    };
    let base = Inputs {
        contexts: Path::new(base_contexts),
        catalogue: Path::new(base_catalogue),
        physical_root: Path::new(base_root),
    };
    let head = Inputs {
        contexts: Path::new(head_contexts),
        catalogue: Path::new(head_catalogue),
        physical_root: Path::new(head_root),
    };
    match (mode.to_str(), tail) {
        (Some("audit-test-classpath-delta"), [context]) => {
            let delta = runtime_equivalence::audit_test_classpath_delta(
                base,
                head,
                context.to_str().ok_or("invalid test context ID")?,
            )?;
            serde_json::to_writer_pretty(std::io::stdout().lock(), &delta)?;
        }
        (Some("compare"), []) => {
            let comparison = runtime_equivalence::compare(base, head)?;
            serde_json::to_writer_pretty(std::io::stdout().lock(), &comparison)?;
        }
        (Some("compare"), [flag]) if flag == "--assume-unchanged-build-stamp" => {
            let comparison = runtime_equivalence::compare_with_policy(
                base,
                head,
                BuildStampPolicy::AssumeUnchanged,
            )?;
            serde_json::to_writer_pretty(std::io::stdout().lock(), &comparison)?;
        }
        (Some("select-tracked-test"), [repo]) => {
            let selection =
                runtime_equivalence::select_tracked_test_delta(base, head, Path::new(repo))?;
            serde_json::to_writer_pretty(std::io::stdout().lock(), &selection)?;
        }
        (Some("select-tracked-test"), [repo, flag]) if flag == "--assume-unchanged-build-stamp" => {
            let selection = runtime_equivalence::select_tracked_test_delta_with_policy(
                base,
                head,
                Path::new(repo),
                BuildStampPolicy::AssumeUnchanged,
            )?;
            serde_json::to_writer_pretty(std::io::stdout().lock(), &selection)?;
        }
        _ => return Err("invalid runtime equivalence mode or arguments".into()),
    }
    println!();
    Ok(())
}
