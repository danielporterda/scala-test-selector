//! Small transactional catalogue; never used for individual analysis operations.
//!
//! Each command/thread owns its SQLite connection. Published artifact bytes live
//! outside SQLite. Register only complete immutable files, then commit references
//! together. WAL permits readers while another connection publishes metadata.

use rusqlite::{Connection, OptionalExtension, Transaction, TransactionBehavior, params};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

const SCHEMA_VERSION: i64 = 1;
const APPLICATION_ID: i64 = 0x5253454c;

#[derive(Debug)]
pub enum Error {
    Sql(rusqlite::Error),
    Io(std::io::Error),
    Artifact(selector_artifacts::Error),
    Invalid(&'static str),
    Conflict(&'static str),
    MissingRun(i64),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Sql(error) => write!(f, "catalogue SQLite: {error}"),
            Self::Io(error) => write!(f, "catalogue I/O: {error}"),
            Self::Artifact(error) => write!(f, "catalogue artifact admission: {error}"),
            Self::Invalid(message) => write!(f, "invalid catalogue data: {message}"),
            Self::Conflict(message) => write!(f, "immutable catalogue entry conflicts: {message}"),
            Self::MissingRun(id) => write!(f, "catalogue run {id} does not exist"),
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Sql(error) => Some(error),
            Self::Io(error) => Some(error),
            Self::Artifact(error) => Some(error),
            _ => None,
        }
    }
}
impl From<rusqlite::Error> for Error {
    fn from(error: rusqlite::Error) -> Self {
        Self::Sql(error)
    }
}
impl From<std::io::Error> for Error {
    fn from(error: std::io::Error) -> Self {
        Self::Io(error)
    }
}
impl From<selector_artifacts::Error> for Error {
    fn from(error: selector_artifacts::Error) -> Self {
        Self::Artifact(error)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactRecord {
    pub identity: [u8; 32],
    /// Stable artifact wire kind, independent of storage implementation enums.
    pub kind: u32,
    /// Current admitted location. Relocation does not change content identity.
    pub path: PathBuf,
    pub bytes: u64,
}
#[derive(Debug, Clone, Copy)]
pub struct CacheKey<'a> {
    pub stage: &'a str,
    pub inputs: [u8; 32],
    pub producer: [u8; 32],
}
#[derive(Debug, Clone)]
pub struct Registration<'a> {
    pub key: CacheKey<'a>,
    pub artifact: ArtifactRecord,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RunStatus {
    Running,
    Complete,
    Incomplete,
    Failed,
}
impl RunStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::Running => "running",
            Self::Complete => "complete",
            Self::Incomplete => "incomplete",
            Self::Failed => "failed",
        }
    }
    fn parse(text: &str) -> Result<Self, Error> {
        match text {
            "running" => Ok(Self::Running),
            "complete" => Ok(Self::Complete),
            "incomplete" => Ok(Self::Incomplete),
            "failed" => Ok(Self::Failed),
            _ => Err(Error::Invalid("run status")),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunRecord {
    pub id: i64,
    pub command: String,
    pub inputs: [u8; 32],
    pub status: RunStatus,
    pub started_at: i64,
    pub finished_at: Option<i64>,
    pub metrics_json: Option<String>,
}

pub struct Catalogue {
    connection: Connection,
}
impl Catalogue {
    pub fn open(path: &Path) -> Result<Self, Error> {
        if let Some(parent) = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
        {
            fs::create_dir_all(parent)?;
        }
        Self::from_connection(Connection::open(path)?)
    }
    pub fn in_memory() -> Result<Self, Error> {
        Self::from_connection(Connection::open_in_memory()?)
    }
    fn from_connection(mut connection: Connection) -> Result<Self, Error> {
        connection.busy_timeout(Duration::from_secs(10))?;
        connection.execute_batch(
            "PRAGMA foreign_keys=ON; PRAGMA journal_mode=WAL; PRAGMA synchronous=FULL;",
        )?;
        let application: i64 =
            connection.query_row("PRAGMA application_id", [], |row| row.get(0))?;
        if application != 0 && application != APPLICATION_ID {
            return Err(Error::Invalid("database belongs to another application"));
        }
        let version: i64 = connection.query_row("PRAGMA user_version", [], |row| row.get(0))?;
        if version != 0 && version != SCHEMA_VERSION {
            return Err(Error::Invalid("unsupported schema version"));
        }
        let transaction = connection.transaction_with_behavior(TransactionBehavior::Immediate)?;
        transaction.execute_batch(
            "CREATE TABLE IF NOT EXISTS artifacts (
                identity BLOB PRIMARY KEY CHECK(length(identity)=32),
                kind INTEGER NOT NULL CHECK(kind>0),
                path TEXT NOT NULL,
                byte_length INTEGER NOT NULL CHECK(byte_length>=0)
            ) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS entries (
                stage TEXT NOT NULL,
                inputs BLOB NOT NULL CHECK(length(inputs)=32),
                producer BLOB NOT NULL CHECK(length(producer)=32),
                artifact BLOB NOT NULL REFERENCES artifacts(identity),
                PRIMARY KEY(stage,inputs,producer)
            ) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS manifests (
                identity BLOB PRIMARY KEY CHECK(length(identity)=32)
            ) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS manifest_artifacts (
                manifest BLOB NOT NULL REFERENCES manifests(identity),
                ordinal INTEGER NOT NULL CHECK(ordinal>=0),
                artifact BLOB NOT NULL REFERENCES artifacts(identity),
                PRIMARY KEY(manifest,ordinal)
            ) WITHOUT ROWID;
            CREATE TABLE IF NOT EXISTS runs (
                id INTEGER PRIMARY KEY,
                command TEXT NOT NULL,
                inputs BLOB NOT NULL CHECK(length(inputs)=32),
                status TEXT NOT NULL CHECK(status IN ('running','complete','incomplete','failed')),
                started_at INTEGER NOT NULL DEFAULT(unixepoch()),
                finished_at INTEGER,
                metrics_json TEXT
            );",
        )?;
        transaction.pragma_update(None, "application_id", APPLICATION_ID)?;
        transaction.pragma_update(None, "user_version", SCHEMA_VERSION)?;
        transaction.commit()?;
        Ok(Self { connection })
    }

    /// One transaction for a batch of admitted stage outputs. A conflicting key
    /// aborts the entire batch; an identical repeat is idempotent.
    pub fn register_many(&mut self, registrations: &[Registration<'_>]) -> Result<(), Error> {
        for registration in registrations {
            validate_file(&registration.artifact)?;
            validate_key(registration.key)?;
        }
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        for registration in registrations {
            register_artifact(&transaction, &registration.artifact)?;
            let key = registration.key;
            let existing: Option<Vec<u8>> = transaction
                .query_row(
                    "SELECT artifact FROM entries WHERE stage=?1 AND inputs=?2 AND producer=?3",
                    params![key.stage, &key.inputs[..], &key.producer[..]],
                    |row| row.get(0),
                )
                .optional()?;
            match existing {
                Some(existing) if existing != registration.artifact.identity => {
                    return Err(Error::Conflict(
                        "stage key has a different artifact identity",
                    ));
                }
                Some(_) => {}
                None => {
                    transaction.execute(
                        "INSERT INTO entries(stage,inputs,producer,artifact) VALUES(?1,?2,?3,?4)",
                        params![
                            key.stage,
                            &key.inputs[..],
                            &key.producer[..],
                            &registration.artifact.identity[..]
                        ],
                    )?;
                }
            }
        }
        transaction.commit()?;
        Ok(())
    }
    pub fn register(&mut self, key: CacheKey<'_>, artifact: ArtifactRecord) -> Result<(), Error> {
        self.register_many(&[Registration { key, artifact }])
    }
    pub fn lookup(&self, key: CacheKey<'_>) -> Result<Option<ArtifactRecord>, Error> {
        validate_key(key)?;
        let row = self.connection.query_row(
            "SELECT a.identity,a.kind,a.path,a.byte_length FROM entries e JOIN artifacts a ON a.identity=e.artifact
             WHERE e.stage=?1 AND e.inputs=?2 AND e.producer=?3",
            params![key.stage, &key.inputs[..], &key.producer[..]], read_artifact
        ).optional()?;
        row.map(convert_artifact).transpose()
    }
    pub fn artifact(&self, identity: &[u8; 32]) -> Result<Option<ArtifactRecord>, Error> {
        let row = self
            .connection
            .query_row(
                "SELECT identity,kind,path,byte_length FROM artifacts WHERE identity=?1",
                [&identity[..]],
                read_artifact,
            )
            .optional()?;
        row.map(convert_artifact).transpose()
    }

    /// Commit a complete ordered snapshot only after all its files exist. No
    /// reader sees a manifest with only a subset of its artifact references.
    pub fn register_manifest(
        &mut self,
        identity: [u8; 32],
        artifacts: &[ArtifactRecord],
    ) -> Result<(), Error> {
        for artifact in artifacts {
            validate_file(artifact)?;
        }
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        let exists: bool = transaction.query_row(
            "SELECT EXISTS(SELECT 1 FROM manifests WHERE identity=?1)",
            [&identity[..]],
            |row| row.get(0),
        )?;
        if exists {
            let mut statement = transaction.prepare(
                "SELECT artifact FROM manifest_artifacts WHERE manifest=?1 ORDER BY ordinal",
            )?;
            let previous: Vec<Vec<u8>> = statement
                .query_map([&identity[..]], |row| row.get(0))?
                .collect::<Result<_, _>>()?;
            if previous.len() != artifacts.len()
                || previous
                    .iter()
                    .zip(artifacts)
                    .any(|(previous, artifact)| previous != &artifact.identity)
            {
                return Err(Error::Conflict("manifest has different ordered artifacts"));
            }
            // Kind and length remain immutable. A newly admitted copy may
            // replace the location shared by every stage/manifest reference.
            for artifact in artifacts {
                register_artifact(&transaction, artifact)?;
            }
        } else {
            transaction.execute(
                "INSERT INTO manifests(identity) VALUES(?1)",
                [&identity[..]],
            )?;
            for (ordinal, artifact) in artifacts.iter().enumerate() {
                register_artifact(&transaction, artifact)?;
                transaction.execute(
                    "INSERT INTO manifest_artifacts(manifest,ordinal,artifact) VALUES(?1,?2,?3)",
                    params![&identity[..], ordinal as i64, &artifact.identity[..]],
                )?;
            }
        }
        transaction.commit()?;
        Ok(())
    }
    pub fn manifest(&self, identity: &[u8; 32]) -> Result<Option<Vec<ArtifactRecord>>, Error> {
        // A read transaction ensures the existence test and members share a view.
        let transaction = self.connection.unchecked_transaction()?;
        let exists: bool = transaction.query_row(
            "SELECT EXISTS(SELECT 1 FROM manifests WHERE identity=?1)",
            [&identity[..]],
            |row| row.get(0),
        )?;
        if !exists {
            return Ok(None);
        }
        let mut statement = transaction.prepare(
            "SELECT a.identity,a.kind,a.path,a.byte_length FROM manifest_artifacts m JOIN artifacts a ON a.identity=m.artifact
             WHERE m.manifest=?1 ORDER BY m.ordinal"
        )?;
        let rows = statement
            .query_map([&identity[..]], read_artifact)?
            .collect::<Result<Vec<_>, _>>()?;
        let artifacts = rows
            .into_iter()
            .map(convert_artifact)
            .collect::<Result<Vec<_>, _>>()?;
        drop(statement);
        transaction.commit()?;
        Ok(Some(artifacts))
    }

    pub fn begin_run(&mut self, command: &str, inputs: [u8; 32]) -> Result<i64, Error> {
        if command.is_empty() {
            return Err(Error::Invalid("empty run command"));
        }
        self.connection.execute(
            "INSERT INTO runs(command,inputs,status) VALUES(?1,?2,'running')",
            params![command, &inputs[..]],
        )?;
        Ok(self.connection.last_insert_rowid())
    }
    pub fn finish_run(
        &mut self,
        id: i64,
        status: RunStatus,
        metrics_json: &str,
    ) -> Result<(), Error> {
        if status == RunStatus::Running {
            return Err(Error::Invalid("finish_run needs a terminal status"));
        }
        let transaction = self
            .connection
            .transaction_with_behavior(TransactionBehavior::Immediate)?;
        let previous: Option<(String, Option<String>)> = transaction
            .query_row(
                "SELECT status,metrics_json FROM runs WHERE id=?1",
                [id],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()?;
        let Some((previous, metrics)) = previous else {
            return Err(Error::MissingRun(id));
        };
        if previous != "running" {
            if previous != status.as_str() || metrics.as_deref() != Some(metrics_json) {
                return Err(Error::Conflict("finished run cannot be rewritten"));
            }
        } else {
            transaction.execute(
                "UPDATE runs SET status=?1,finished_at=unixepoch(),metrics_json=?2 WHERE id=?3",
                params![status.as_str(), metrics_json, id],
            )?;
        }
        transaction.commit()?;
        Ok(())
    }
    pub fn run(&self, id: i64) -> Result<Option<RunRecord>, Error> {
        type RawRun = (
            i64,
            String,
            Vec<u8>,
            String,
            i64,
            Option<i64>,
            Option<String>,
        );
        let row: Option<RawRun> = self.connection.query_row(
            "SELECT id,command,inputs,status,started_at,finished_at,metrics_json FROM runs WHERE id=?1", [id],
            |row| Ok((row.get(0)?,row.get(1)?,row.get(2)?,row.get(3)?,row.get(4)?,row.get(5)?,row.get(6)?))
        ).optional()?;
        row.map(|row| {
            Ok(RunRecord {
                id: row.0,
                command: row.1,
                inputs: row
                    .2
                    .try_into()
                    .map_err(|_| Error::Invalid("run input identity"))?,
                status: RunStatus::parse(&row.3)?,
                started_at: row.4,
                finished_at: row.5,
                metrics_json: row.6,
            })
        })
        .transpose()
    }
}
fn validate_key(key: CacheKey<'_>) -> Result<(), Error> {
    if key.stage.is_empty() {
        return Err(Error::Invalid("empty stage name"));
    }
    Ok(())
}
fn validate_file(artifact: &ArtifactRecord) -> Result<(), Error> {
    if artifact.bytes > i64::MAX as u64 {
        return Err(Error::Invalid("artifact byte length or kind"));
    }
    let kind = artifact_kind(artifact.kind)?;
    if artifact.path.to_str().is_none() {
        return Err(Error::Invalid("artifact path is not UTF-8"));
    }
    let metadata = fs::metadata(&artifact.path)?;
    if !metadata.is_file() || metadata.len() != artifact.bytes {
        return Err(Error::Invalid(
            "artifact is missing, incomplete, or has a different length",
        ));
    }
    let verified = selector_artifacts::verify_file(
        &artifact.path,
        kind,
        artifact.bytes.min(selector_artifacts::DEFAULT_MAX_BYTES),
    )?;
    if verified.identity != artifact.identity || verified.byte_len != artifact.bytes {
        return Err(Error::Invalid(
            "artifact identity or byte length differs from admitted content",
        ));
    }
    Ok(())
}
fn artifact_kind(kind: u32) -> Result<selector_artifacts::ArtifactKind, Error> {
    use selector_artifacts::ArtifactKind;
    match kind {
        1 => Ok(ArtifactKind::Facts),
        2 => Ok(ArtifactKind::Graph),
        3 => Ok(ArtifactKind::Summaries),
        _ => Err(Error::Invalid("unsupported artifact kind")),
    }
}
fn register_artifact(
    transaction: &Transaction<'_>,
    artifact: &ArtifactRecord,
) -> Result<(), Error> {
    let previous = transaction
        .query_row(
            "SELECT identity,kind,path,byte_length FROM artifacts WHERE identity=?1",
            [&artifact.identity[..]],
            read_artifact,
        )
        .optional()?;
    if let Some(previous) = previous {
        let previous = convert_artifact(previous)?;
        if previous.kind != artifact.kind || previous.bytes != artifact.bytes {
            return Err(Error::Conflict("artifact identity has different metadata"));
        }
        if previous.path != artifact.path {
            // The caller already checksummed the new immutable file. Do not
            // require the old location to exist or rehash it: it may have been
            // moved, and producer changes can legitimately publish identical
            // bytes at a different content-addressed stage path. The update and
            // all new references commit together in this transaction.
            transaction.execute(
                "UPDATE artifacts SET path=?1 WHERE identity=?2",
                params![artifact.path.to_str().unwrap(), &artifact.identity[..]],
            )?;
        }
    } else {
        transaction.execute(
            "INSERT INTO artifacts(identity,kind,path,byte_length) VALUES(?1,?2,?3,?4)",
            params![
                &artifact.identity[..],
                i64::from(artifact.kind),
                artifact.path.to_str().unwrap(),
                artifact.bytes as i64
            ],
        )?;
    }
    Ok(())
}
type RawArtifact = (Vec<u8>, i64, String, i64);
fn read_artifact(row: &rusqlite::Row<'_>) -> rusqlite::Result<RawArtifact> {
    Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?))
}
fn convert_artifact(row: RawArtifact) -> Result<ArtifactRecord, Error> {
    let kind = u32::try_from(row.1).map_err(|_| Error::Invalid("artifact kind"))?;
    artifact_kind(kind)?;
    Ok(ArtifactRecord {
        identity: row
            .0
            .try_into()
            .map_err(|_| Error::Invalid("artifact identity length"))?,
        kind,
        path: PathBuf::from(row.2),
        bytes: u64::try_from(row.3).map_err(|_| Error::Invalid("artifact length"))?,
    })
}
