use selector_catalogue::{ArtifactRecord, CacheKey, Catalogue, Error, Registration, RunStatus};
use std::fs;
use std::path::Path;
use std::sync::{Arc, Barrier};

fn artifact(directory: &Path, byte: u8) -> ArtifactRecord {
    artifact_of_kind(directory, byte, selector_artifacts::ArtifactKind::Facts)
}
fn artifact_of_kind(
    directory: &Path,
    byte: u8,
    kind: selector_artifacts::ArtifactKind,
) -> ArtifactRecord {
    let path = directory.join(format!("{byte}-{}.artifact", kind as u32));
    let identity = selector_artifacts::write(
        &path,
        kind,
        &[selector_artifacts::Section {
            id: 1,
            count: 8,
            bytes: &[byte; 8],
        }],
    )
    .unwrap();
    ArtifactRecord {
        identity,
        kind: kind as u32,
        bytes: fs::metadata(&path).unwrap().len(),
        path,
    }
}
fn key(stage: &str) -> CacheKey<'_> {
    CacheKey {
        stage,
        inputs: [2; 32],
        producer: [3; 32],
    }
}

#[test]
fn stage_reuse_is_specific_and_batch_conflicts_rollback() {
    let temporary = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let first = artifact(temporary.path(), 1);
    let second = artifact(temporary.path(), 2);
    catalogue.register(key("facts"), first.clone()).unwrap();
    assert_eq!(catalogue.lookup(key("facts")).unwrap(), Some(first.clone()));
    assert!(
        catalogue
            .lookup(CacheKey {
                producer: [4; 32],
                ..key("facts")
            })
            .unwrap()
            .is_none()
    );
    assert!(
        catalogue
            .lookup(CacheKey {
                inputs: [4; 32],
                ..key("facts")
            })
            .unwrap()
            .is_none()
    );
    catalogue.register(key("facts"), first.clone()).unwrap();
    assert!(matches!(
        catalogue.register_many(&[
            Registration {
                key: key("graph"),
                artifact: second.clone()
            },
            Registration {
                key: key("facts"),
                artifact: second.clone()
            },
        ]),
        Err(Error::Conflict(_))
    ));
    assert!(catalogue.lookup(key("graph")).unwrap().is_none());
    assert!(catalogue.artifact(&second.identity).unwrap().is_none());
    assert_eq!(catalogue.lookup(key("facts")).unwrap(), Some(first));
}

#[test]
fn manifest_is_atomic_ordered_immutable_and_can_be_empty() {
    let temporary = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let first = artifact(temporary.path(), 1);
    let second = artifact(temporary.path(), 2);
    let absent = ArtifactRecord {
        path: temporary.path().join("absent"),
        ..first.clone()
    };
    assert!(
        catalogue
            .register_manifest([9; 32], &[first.clone(), absent])
            .is_err()
    );
    assert!(catalogue.manifest(&[9; 32]).unwrap().is_none());
    assert!(catalogue.artifact(&first.identity).unwrap().is_none());
    catalogue
        .register_manifest([9; 32], &[first.clone(), second.clone()])
        .unwrap();
    catalogue
        .register_manifest([9; 32], &[first.clone(), second.clone()])
        .unwrap();
    assert_eq!(
        catalogue.manifest(&[9; 32]).unwrap().unwrap(),
        [first.clone(), second.clone()]
    );
    assert!(
        catalogue
            .register_manifest([9; 32], &[second, first])
            .is_err()
    );
    catalogue.register_manifest([8; 32], &[]).unwrap();
    assert_eq!(catalogue.manifest(&[8; 32]).unwrap(), Some(vec![]));
}

#[test]
fn run_status_is_terminal_idempotent_and_survives_reopen() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("catalogue.sqlite");
    let mut catalogue = Catalogue::open(&path).unwrap();
    let id = catalogue.begin_run("query", [7; 32]).unwrap();
    assert_eq!(
        catalogue.run(id).unwrap().unwrap().status,
        RunStatus::Running
    );
    catalogue
        .finish_run(id, RunStatus::Incomplete, "{\"budget\":true}")
        .unwrap();
    catalogue
        .finish_run(id, RunStatus::Incomplete, "{\"budget\":true}")
        .unwrap();
    assert!(matches!(
        catalogue.finish_run(id, RunStatus::Complete, "{}"),
        Err(Error::Conflict(_))
    ));
    assert!(matches!(
        catalogue.finish_run(999, RunStatus::Failed, "{}"),
        Err(Error::MissingRun(999))
    ));
    drop(catalogue);
    let catalogue = Catalogue::open(&path).unwrap();
    let record = catalogue.run(id).unwrap().unwrap();
    assert_eq!(record.inputs, [7; 32]);
    assert_eq!(record.status, RunStatus::Incomplete);
    assert!(record.finished_at.is_some());
}

#[test]
fn parallel_connections_publish_complete_batches_with_readers() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("catalogue.sqlite");
    Catalogue::open(&path).unwrap();
    let records: Vec<_> = (1..=8)
        .map(|value| artifact(temporary.path(), value))
        .collect();
    let barrier = Arc::new(Barrier::new(9));
    let threads: Vec<_> = records
        .into_iter()
        .enumerate()
        .map(|(index, artifact)| {
            let barrier = barrier.clone();
            let path = path.clone();
            std::thread::spawn(move || {
                let mut catalogue = Catalogue::open(&path).unwrap();
                barrier.wait();
                catalogue
                    .register(
                        CacheKey {
                            inputs: [index as u8; 32],
                            ..key("facts")
                        },
                        artifact,
                    )
                    .unwrap();
            })
        })
        .collect();
    let catalogue = Catalogue::open(&path).unwrap();
    barrier.wait();
    for _ in 0..10 {
        for index in 0..8 {
            let _ = catalogue
                .lookup(CacheKey {
                    inputs: [index; 32],
                    ..key("facts")
                })
                .unwrap();
        }
    }
    for thread in threads {
        thread.join().unwrap();
    }
    for index in 0..8 {
        assert!(
            catalogue
                .lookup(CacheKey {
                    inputs: [index; 32],
                    ..key("facts")
                })
                .unwrap()
                .is_some()
        );
    }
}

#[test]
fn incomplete_artifacts_and_foreign_database_are_rejected() {
    let temporary = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let mut record = artifact(temporary.path(), 1);
    record.bytes += 1;
    assert!(catalogue.register(key("facts"), record).is_err());
    let path = temporary.path().join("foreign.sqlite");
    let connection = rusqlite::Connection::open(&path).unwrap();
    connection
        .pragma_update(None, "application_id", 123)
        .unwrap();
    drop(connection);
    assert!(matches!(Catalogue::open(&path), Err(Error::Invalid(_))));
}

#[test]
fn full_checksum_claimed_identity_and_kind_are_admitted_before_any_commit() {
    let directory = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let good = artifact(directory.path(), 10);
    let corrupt = artifact(directory.path(), 11);
    let mut bytes = fs::read(&corrupt.path).unwrap();
    *bytes.last_mut().unwrap() ^= 1;
    fs::remove_file(&corrupt.path).unwrap();
    fs::write(&corrupt.path, &bytes).unwrap();
    assert!(
        catalogue
            .register_manifest([8; 32], &[good.clone(), corrupt.clone()])
            .is_err()
    );
    assert!(catalogue.manifest(&[8; 32]).unwrap().is_none());
    assert!(catalogue.artifact(&good.identity).unwrap().is_none());
    assert!(catalogue.register(key("corrupt"), corrupt).is_err());
    assert!(catalogue.lookup(key("corrupt")).unwrap().is_none());
    for wrong in [
        ArtifactRecord {
            identity: [99; 32],
            ..good.clone()
        },
        ArtifactRecord {
            kind: 2,
            ..good.clone()
        },
        ArtifactRecord {
            kind: 0,
            ..good.clone()
        },
        ArtifactRecord {
            kind: 4,
            ..good.clone()
        },
    ] {
        assert!(catalogue.register(key("invalid"), wrong).is_err());
    }
    assert!(catalogue.lookup(key("invalid")).unwrap().is_none());
}

#[test]
fn summaries_are_a_recognized_checksummed_artifact_kind() {
    let directory = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let summary = artifact_of_kind(
        directory.path(),
        12,
        selector_artifacts::ArtifactKind::Summaries,
    );
    catalogue
        .register(key("summary/v1"), summary.clone())
        .unwrap();
    assert_eq!(
        catalogue.lookup(key("summary/v1")).unwrap(),
        Some(summary.clone())
    );
    catalogue
        .register_manifest([12; 32], &[summary.clone()])
        .unwrap();
    assert_eq!(catalogue.manifest(&[12; 32]).unwrap(), Some(vec![summary]));
}

#[test]
fn producer_change_and_repeated_manifest_can_relocate_identical_content() {
    let directory = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let original = artifact(directory.path(), 13);
    catalogue
        .register_manifest([13; 32], &[original.clone()])
        .unwrap();
    catalogue.register(key("facts"), original.clone()).unwrap();
    let path = directory.path().join("alias");
    fs::copy(&original.path, &path).unwrap();
    let alias = ArtifactRecord {
        path,
        ..original.clone()
    };
    let changed_producer = CacheKey {
        producer: [4; 32],
        ..key("facts")
    };
    catalogue.register(changed_producer, alias.clone()).unwrap();
    assert_eq!(catalogue.lookup(key("facts")).unwrap(), Some(alias.clone()));
    assert_eq!(
        catalogue.lookup(changed_producer).unwrap(),
        Some(alias.clone())
    );
    assert_eq!(
        catalogue.manifest(&[13; 32]).unwrap(),
        Some(vec![alias.clone()])
    );
    catalogue
        .register_manifest([13; 32], &[original.clone()])
        .unwrap();
    assert_eq!(catalogue.lookup(changed_producer).unwrap(), Some(original));
}

#[test]
fn missing_old_location_is_repaired_without_changing_existing_bindings() {
    let directory = tempfile::tempdir().unwrap();
    let database = directory.path().join("catalogue.sqlite");
    let mut catalogue = Catalogue::open(&database).unwrap();
    let original = artifact(directory.path(), 14);
    catalogue.register(key("facts"), original.clone()).unwrap();
    catalogue
        .register_manifest([14; 32], &[original.clone()])
        .unwrap();
    let alias = ArtifactRecord {
        path: directory.path().join("relocated"),
        ..original.clone()
    };
    fs::copy(&original.path, &alias.path).unwrap();
    fs::remove_file(&original.path).unwrap();
    let next = CacheKey {
        producer: [8; 32],
        ..key("facts")
    };
    catalogue.register(next, alias.clone()).unwrap();
    drop(catalogue);
    let catalogue = Catalogue::open(&database).unwrap();
    assert_eq!(catalogue.lookup(key("facts")).unwrap(), Some(alias.clone()));
    assert_eq!(catalogue.lookup(next).unwrap(), Some(alias.clone()));
    assert_eq!(
        catalogue.manifest(&[14; 32]).unwrap(),
        Some(vec![alias.clone()])
    );
    assert_eq!(
        selector_artifacts::verify_file(
            &alias.path,
            selector_artifacts::ArtifactKind::Facts,
            alias.bytes
        )
        .unwrap()
        .identity,
        original.identity
    );
}

#[test]
fn relocation_and_stage_bindings_roll_back_on_later_batch_conflict() {
    let directory = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let original = artifact(directory.path(), 15);
    let different = artifact(directory.path(), 16);
    catalogue.register(key("facts"), original.clone()).unwrap();
    let alias = ArtifactRecord {
        path: directory.path().join("alias"),
        ..original.clone()
    };
    fs::copy(&original.path, &alias.path).unwrap();
    let next = CacheKey {
        producer: [5; 32],
        ..key("facts")
    };
    assert!(matches!(
        catalogue.register_many(&[
            Registration {
                key: next,
                artifact: alias
            },
            Registration {
                key: key("facts"),
                artifact: different
            },
        ]),
        Err(Error::Conflict(_))
    ));
    assert_eq!(catalogue.lookup(key("facts")).unwrap(), Some(original));
    assert!(catalogue.lookup(next).unwrap().is_none());
}

#[test]
fn relocation_still_requires_exact_kind_size_and_checksum() {
    let directory = tempfile::tempdir().unwrap();
    let mut catalogue = Catalogue::in_memory().unwrap();
    let original = artifact(directory.path(), 17);
    catalogue.register(key("facts"), original.clone()).unwrap();
    let alias = ArtifactRecord {
        path: directory.path().join("alias"),
        ..original.clone()
    };
    fs::copy(&original.path, &alias.path).unwrap();
    let next = CacheKey {
        producer: [6; 32],
        ..key("facts")
    };
    for forged in [
        ArtifactRecord {
            kind: 2,
            ..alias.clone()
        },
        ArtifactRecord {
            bytes: alias.bytes + 1,
            ..alias.clone()
        },
    ] {
        assert!(catalogue.register(next, forged).is_err());
    }
    let mut corrupt = fs::read(&alias.path).unwrap();
    *corrupt.last_mut().unwrap() ^= 1;
    fs::remove_file(&alias.path).unwrap();
    fs::write(&alias.path, corrupt).unwrap();
    assert!(catalogue.register(next, alias).is_err());
    assert_eq!(catalogue.lookup(key("facts")).unwrap(), Some(original));
    assert!(catalogue.lookup(next).unwrap().is_none());
}
