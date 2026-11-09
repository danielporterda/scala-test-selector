use selector_artifacts::{
    ArtifactKind, DEFAULT_MAX_BYTES, Error, MAX_SECTIONS, Section, StreamingSection, open,
    open_bounded, publish, verify_file, write, write_streaming,
};
use sha2::{Digest, Sha256};
use std::fs;
use std::io;
use std::sync::{Arc, Barrier};

fn sample(path: &std::path::Path) -> [u8; 32] {
    write(
        path,
        ArtifactKind::Facts,
        &[
            Section {
                id: 8,
                count: 3,
                bytes: b"abc",
            },
            Section {
                id: 2,
                count: 2,
                bytes: b"two records",
            },
            Section {
                id: 15,
                count: 0,
                bytes: b"",
            },
        ],
    )
    .unwrap()
}
fn mutate(path: &std::path::Path, change: impl FnOnce(&mut Vec<u8>), checksum: bool) {
    let mut bytes = fs::read(path).unwrap();
    change(&mut bytes);
    if checksum {
        bytes[40..72].fill(0);
        let hash: [u8; 32] = Sha256::digest(&bytes).into();
        bytes[40..72].copy_from_slice(&hash);
    }
    fs::remove_file(path).unwrap(); // Never overwrite an immutable mapped inode.
    fs::write(path, bytes).unwrap();
}

#[test]
fn roundtrip_sorted_sections_zero_copy_and_idempotent_publication() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("facts");
    let identity = sample(&path);
    let artifact = open(&path, ArtifactKind::Facts).unwrap();
    assert_eq!(identity, artifact.identity());
    assert_eq!(artifact.section_ids().collect::<Vec<_>>(), [2, 8, 15]);
    assert_eq!(artifact.section(2).unwrap(), b"two records");
    assert_eq!(artifact.count(2).unwrap(), 2);
    assert_eq!(artifact.section(15).unwrap(), []);
    assert_eq!(
        artifact.section(8).unwrap().as_ptr(),
        artifact.section(8).unwrap().as_ptr()
    );
    assert!(matches!(artifact.section(7), Err(Error::MissingSection(7))));
    assert_eq!(sample(&path), identity);
    assert!(matches!(
        write(
            &path,
            ArtifactKind::Facts,
            &[Section {
                id: 2,
                count: 1,
                bytes: b"different"
            }]
        ),
        Err(Error::Conflict(_))
    ));
    assert_eq!(
        open(&path, ArtifactKind::Facts).unwrap().identity(),
        identity
    );
    assert!(fs::read_dir(temporary.path()).unwrap().all(|entry| {
        !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .ends_with(".tmp")
    }));
}

#[test]
fn admission_rejects_corruption_and_structural_lies_even_with_valid_outer_hash() {
    let temporary = tempfile::tempdir().unwrap();
    let cases: Vec<Box<dyn Fn(&mut Vec<u8>)>> = vec![
        Box::new(|bytes| bytes[0] ^= 1),
        Box::new(|bytes| bytes[8..12].copy_from_slice(&99u32.to_le_bytes())),
        Box::new(|bytes| bytes[16..20].copy_from_slice(&u32::MAX.to_le_bytes())),
        Box::new(|bytes| bytes[24..32].copy_from_slice(&u64::MAX.to_le_bytes())),
        Box::new(|bytes| bytes[32..40].copy_from_slice(&u64::MAX.to_le_bytes())),
        Box::new(|bytes| bytes[72] = 1),
        Box::new(|bytes| bytes[80 + 4] = 1),
        Box::new(|bytes| bytes[80 + 16..80 + 24].copy_from_slice(&0u64.to_le_bytes())),
        Box::new(|bytes| bytes[80 + 24..80 + 32].copy_from_slice(&u64::MAX.to_le_bytes())),
        Box::new(|bytes| bytes[144..148].copy_from_slice(&2u32.to_le_bytes())),
        Box::new(|bytes| bytes[144 + 16..144 + 24].copy_from_slice(&272u64.to_le_bytes())),
        Box::new(|bytes| {
            let last = bytes.len() - 1;
            bytes[last] ^= 1;
        }),
        Box::new(|bytes| bytes.push(0)),
    ];
    for (index, case) in cases.into_iter().enumerate() {
        let path = temporary.path().join(format!("corrupt-{index}"));
        sample(&path);
        mutate(&path, case, true);
        assert!(
            open(&path, ArtifactKind::Facts).is_err(),
            "corruption case {index}"
        );
        assert!(
            verify_file(&path, ArtifactKind::Facts, DEFAULT_MAX_BYTES).is_err(),
            "streaming corruption case {index}"
        );
    }
    let path = temporary.path().join("digest");
    sample(&path);
    mutate(&path, |bytes| bytes[40] ^= 1, false);
    assert!(matches!(
        open(&path, ArtifactKind::Facts),
        Err(Error::Checksum { section: None })
    ));
    assert!(matches!(
        verify_file(&path, ArtifactKind::Facts, DEFAULT_MAX_BYTES),
        Err(Error::Checksum { section: None })
    ));
}

#[test]
fn bounded_streaming_admission_matches_owned_for_all_wire_kinds() {
    let directory = tempfile::tempdir().unwrap();
    for kind in [
        ArtifactKind::Facts,
        ArtifactKind::Graph,
        ArtifactKind::Summaries,
        ArtifactKind::Continuation,
        ArtifactKind::Effects,
    ] {
        let path = directory.path().join(format!("kind-{}", kind as u32));
        let bytes = vec![0x9a; 300_001];
        let identity = write(
            &path,
            kind,
            &[
                Section {
                    id: 1,
                    count: 0,
                    bytes: b"",
                },
                Section {
                    id: 3,
                    count: bytes.len() as u64,
                    bytes: &bytes,
                },
                Section {
                    id: 5,
                    count: 1,
                    bytes: b"tail",
                },
            ],
        )
        .unwrap();
        let verified = verify_file(&path, kind, DEFAULT_MAX_BYTES).unwrap();
        assert_eq!(verified.identity, identity);
        assert_eq!(verified.byte_len, fs::metadata(&path).unwrap().len());
        assert_eq!(verified.kind, kind);
        assert_eq!(open(&path, kind).unwrap().identity(), identity);
        assert!(matches!(
            verify_file(&path, kind, 80),
            Err(Error::Limit { .. })
        ));
    }
}

#[test]
fn effect_inputs_and_query_outputs_cannot_be_admitted_as_each_other() {
    let directory = tempfile::tempdir().unwrap();
    for kind in [
        ArtifactKind::Effects,
        ArtifactKind::Summaries,
        ArtifactKind::Continuation,
    ] {
        let path = directory.path().join(format!("separate-{}", kind as u32));
        write(
            &path,
            kind,
            &[Section {
                id: 1,
                count: 1,
                bytes: b"identical payload",
            }],
        )
        .unwrap();
        for other in [
            ArtifactKind::Effects,
            ArtifactKind::Summaries,
            ArtifactKind::Continuation,
        ] {
            if kind == other {
                assert!(open(&path, other).is_ok());
                assert!(verify_file(&path, other, DEFAULT_MAX_BYTES).is_ok());
            } else {
                assert!(matches!(open(&path, other), Err(Error::Kind { .. })));
                assert!(matches!(
                    verify_file(&path, other, DEFAULT_MAX_BYTES),
                    Err(Error::Kind { .. })
                ));
            }
        }
    }
}

#[test]
fn directory_limit_and_nonzero_padding_reject_before_admission() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("directory");
    sample(&path);
    mutate(
        &path,
        |bytes| bytes[16..20].copy_from_slice(&((MAX_SECTIONS + 1) as u32).to_le_bytes()),
        true,
    );
    assert!(matches!(
        open(&path, ArtifactKind::Facts),
        Err(Error::Format("section directory limit"))
    ));
    assert!(matches!(
        verify_file(&path, ArtifactKind::Facts, DEFAULT_MAX_BYTES),
        Err(Error::Format("section directory limit"))
    ));
    let path = directory.path().join("padding");
    sample(&path);
    mutate(&path, |bytes| bytes[283] = 1, true);
    assert!(matches!(
        open(&path, ArtifactKind::Facts),
        Err(Error::Format("nonzero section padding"))
    ));
    assert!(matches!(
        verify_file(&path, ArtifactKind::Facts, DEFAULT_MAX_BYTES),
        Err(Error::Format("nonzero section padding"))
    ));
    let many: Vec<_> = (0..=MAX_SECTIONS)
        .map(|id| Section {
            id: id as u32,
            count: 0,
            bytes: &[],
        })
        .collect();
    assert!(
        write(
            &directory.path().join("too-many"),
            ArtifactKind::Facts,
            &many
        )
        .is_err()
    );
}

#[test]
fn kind_size_truncation_and_duplicate_ids_fail() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("facts");
    sample(&path);
    assert!(matches!(
        open(&path, ArtifactKind::Graph),
        Err(Error::Kind { .. })
    ));
    assert!(matches!(
        open_bounded(&path, ArtifactKind::Facts, 80),
        Err(Error::Limit { .. })
    ));
    assert!(
        write(
            &temporary.path().join("duplicate"),
            ArtifactKind::Facts,
            &[
                Section {
                    id: 1,
                    count: 0,
                    bytes: b""
                },
                Section {
                    id: 1,
                    count: 0,
                    bytes: b""
                }
            ]
        )
        .is_err()
    );
    mutate(&path, |bytes| bytes.truncate(79), false);
    assert!(open(&path, ArtifactKind::Facts).is_err());
}

#[test]
fn owned_reader_does_not_borrow_mutable_input() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("facts");
    sample(&path);
    let artifact = open(&path, ArtifactKind::Facts).unwrap();
    fs::remove_file(&path).unwrap();
    fs::write(&path, b"replacement").unwrap();
    assert_eq!(artifact.section(8).unwrap(), b"abc");
}

#[test]
fn concurrent_content_publication_has_one_complete_identity() {
    let temporary = tempfile::tempdir().unwrap();
    let directory = temporary.path().to_path_buf();
    let barrier = Arc::new(Barrier::new(8));
    let handles: Vec<_> = (0..8)
        .map(|_| {
            let directory = directory.clone();
            let barrier = barrier.clone();
            std::thread::spawn(move || {
                barrier.wait();
                publish(
                    &directory,
                    ArtifactKind::Graph,
                    &[Section {
                        id: 1,
                        count: 4,
                        bytes: b"data",
                    }],
                )
                .unwrap()
            })
        })
        .collect();
    let results: Vec<_> = handles
        .into_iter()
        .map(|handle| handle.join().unwrap())
        .collect();
    for result in &results {
        assert_eq!(result.identity, results[0].identity);
        assert_eq!(result.path, results[0].path);
    }
    assert_eq!(fs::read_dir(&directory).unwrap().count(), 1);
    assert_eq!(
        open(&results[0].path, ArtifactKind::Graph)
            .unwrap()
            .section(1)
            .unwrap(),
        b"data"
    );
}

#[cfg(unix)]
#[test]
fn mapping_owns_immutable_unlinked_inode_and_is_shared_across_workers() {
    let temporary = tempfile::tempdir().unwrap();
    let path = temporary.path().join("facts");
    sample(&path);
    // SAFETY: this test controls all access to the inode, never changes its bytes,
    // and unlinks the sole name while the mapped owner retains its descriptor.
    let artifact = Arc::new(unsafe {
        selector_artifacts::open_mapped_immutable(&path, ArtifactKind::Facts, 1024).unwrap()
    });
    fs::remove_file(&path).unwrap();
    assert!(artifact.is_mapped());
    let threads: Vec<_> = (0..4)
        .map(|_| {
            let artifact = artifact.clone();
            std::thread::spawn(move || {
                for _ in 0..10000 {
                    assert_eq!(artifact.section(2).unwrap(), b"two records");
                }
            })
        })
        .collect();
    for thread in threads {
        thread.join().unwrap();
    }
}

#[test]
fn streaming_encoder_matches_regular_bytes_without_staging_and_fails_atomically() {
    let temporary = tempfile::tempdir().unwrap();
    let regular = temporary.path().join("regular");
    let streamed = temporary.path().join("streamed");
    let first = sample(&regular);
    let sections = [
        StreamingSection {
            id: 8,
            count: 3,
            length: 3,
        },
        StreamingSection {
            id: 2,
            count: 2,
            length: 11,
        },
        StreamingSection {
            id: 15,
            count: 0,
            length: 0,
        },
    ];
    let second = write_streaming(&streamed, ArtifactKind::Facts, &sections, |id, output| {
        output.write_all(match id {
            8 => b"abc",
            2 => b"two records",
            15 => b"",
            _ => unreachable!(),
        })
    })
    .unwrap();
    assert_eq!(first, second);
    assert_eq!(fs::read(&regular).unwrap(), fs::read(&streamed).unwrap());
    let failed = temporary.path().join("failed");
    let mut call = 0;
    assert!(
        write_streaming(
            &failed,
            ArtifactKind::Facts,
            &[StreamingSection {
                id: 1,
                count: 1,
                length: 1
            }],
            |_, output| {
                call += 1;
                output.write_all(&[call])
            }
        )
        .is_err()
    );
    assert!(!failed.exists());
    assert!(
        write_streaming(&failed, ArtifactKind::Facts, &sections, |_, _| Err(
            io::Error::other("encoder failure")
        ))
        .is_err()
    );
    assert!(!failed.exists());
    assert!(
        write_streaming(
            &failed,
            ArtifactKind::Facts,
            &[StreamingSection {
                id: 1,
                count: 1,
                length: 1
            }],
            |_, output| output.write_all(b"overrun")
        )
        .is_err()
    );
    assert!(!failed.exists());
}

#[test]
fn streaming_scalar_batches_and_large_chunks_produce_identical_content() {
    let temporary = tempfile::tempdir().unwrap();
    let bytes: Vec<u8> = (0..100_000).map(|index| (index % 251) as u8).collect();
    let regular = write(
        &temporary.path().join("regular-large"),
        ArtifactKind::Graph,
        &[Section {
            id: 1,
            count: 100_000,
            bytes: &bytes,
        }],
    )
    .unwrap();
    let streamed = write_streaming(
        &temporary.path().join("streamed-large"),
        ArtifactKind::Graph,
        &[StreamingSection {
            id: 1,
            count: 100_000,
            length: 100_000,
        }],
        |_, output| {
            output.write_all(&bytes[..20_000])?;
            for byte in &bytes[20_000..80_000] {
                output.write_all(&[*byte])?;
            }
            output.flush()?;
            output.write_all(&bytes[80_000..])
        },
    )
    .unwrap();
    assert_eq!(regular, streamed);
}
