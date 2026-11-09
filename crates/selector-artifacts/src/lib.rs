//! Immutable, versioned analysis artifacts. Runtime layouts are never disk layouts.
//!
//! The ordinary reader owns one byte buffer and is safe for arbitrary inputs.
//! Mapping is deliberately an unsafe opt-in: read-only protection does not prevent
//! another file descriptor from truncating the backing file. A checksum cannot
//! discharge that lifetime obligation. The publisher never overwrites an artifact.

use sha2::{Digest, Sha256};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

const MAGIC: &[u8; 8] = b"RSELART\0";
const VERSION: u32 = 1;
const HEADER_BYTES: usize = 80;
const SECTION_BYTES: usize = 64;
const CHECKSUM_START: usize = 40;
const CHECKSUM_END: usize = 72;
pub const DEFAULT_MAX_BYTES: u64 = 4 * 1024 * 1024 * 1024;
/// Known schemas use fewer than 16 sections; cap untrusted directory allocations.
pub const MAX_SECTIONS: usize = 4096;
static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum ArtifactKind {
    Facts = 1,
    Graph = 2,
    Summaries = 3,
    /// Incomplete query state has its own schema and cannot admit as summaries.
    Continuation = 4,
    /// Potential effects are independently admitted inputs, not solver summaries.
    Effects = 5,
}

#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    Format(&'static str),
    Kind { expected: ArtifactKind, actual: u32 },
    Checksum { section: Option<u32> },
    MissingSection(u32),
    Limit { size: u64, maximum: u64 },
    Conflict(PathBuf),
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(error) => write!(f, "artifact I/O: {error}"),
            Self::Format(message) => write!(f, "invalid artifact: {message}"),
            Self::Kind { expected, actual } => {
                write!(f, "artifact kind {actual}, expected {expected:?}")
            }
            Self::Checksum { section: Some(id) } => {
                write!(f, "artifact section {id} checksum mismatch")
            }
            Self::Checksum { section: None } => f.write_str("artifact checksum mismatch"),
            Self::MissingSection(id) => write!(f, "artifact section {id} is missing"),
            Self::Limit { size, maximum } => {
                write!(f, "artifact needs {size} bytes, limit is {maximum}")
            }
            Self::Conflict(path) => write!(
                f,
                "immutable artifact already has different content: {}",
                path.display()
            ),
        }
    }
}
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Io(error) => Some(error),
            _ => None,
        }
    }
}
impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::Io(error)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Section<'a> {
    pub id: u32,
    pub count: u64,
    pub bytes: &'a [u8],
}
#[derive(Debug, Clone)]
struct SectionMeta {
    id: u32,
    count: u64,
    offset: usize,
    length: usize,
    checksum: [u8; 32],
}

enum Storage {
    Owned(Vec<u8>),
    #[cfg(unix)]
    Mapped(mapping::Mapping),
}
impl Storage {
    fn bytes(&self) -> &[u8] {
        match self {
            Self::Owned(bytes) => bytes,
            #[cfg(unix)]
            Self::Mapped(mapping) => mapping.bytes(),
        }
    }
}

/// Owns the backing bytes. Returned slices cannot outlive this owner. Cloning a
/// graph must share this owner (for example through `Arc`), not clone its bytes.
pub struct Artifact {
    storage: Storage,
    identity: [u8; 32],
    kind: ArtifactKind,
    sections: Vec<SectionMeta>,
}
impl fmt::Debug for Artifact {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Artifact")
            .field("identity", &identity_hex(&self.identity))
            .field("kind", &self.kind)
            .field("bytes", &self.byte_len())
            .field("sections", &self.sections.len())
            .finish()
    }
}
impl Artifact {
    pub fn section(&self, id: u32) -> Result<&[u8], Error> {
        let meta = self.meta(id)?;
        Ok(&self.storage.bytes()[meta.offset..meta.offset + meta.length])
    }
    pub fn count(&self, id: u32) -> Result<u64, Error> {
        Ok(self.meta(id)?.count)
    }
    pub fn identity(&self) -> [u8; 32] {
        self.identity
    }
    pub fn kind(&self) -> ArtifactKind {
        self.kind
    }
    pub fn byte_len(&self) -> usize {
        self.storage.bytes().len()
    }
    pub fn section_ids(&self) -> impl ExactSizeIterator<Item = u32> + '_ {
        self.sections.iter().map(|section| section.id)
    }
    pub fn is_mapped(&self) -> bool {
        match self.storage {
            Storage::Owned(_) => false,
            #[cfg(unix)]
            Storage::Mapped(_) => true,
        }
    }
    fn meta(&self, id: u32) -> Result<&SectionMeta, Error> {
        self.sections
            .binary_search_by_key(&id, |entry| entry.id)
            .map(|index| &self.sections[index])
            .map_err(|_| Error::MissingSection(id))
    }
}

pub fn identity_hex(identity: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut text = String::with_capacity(64);
    for &byte in identity {
        text.push(HEX[(byte >> 4) as usize] as char);
        text.push(HEX[(byte & 15) as usize] as char);
    }
    text
}

/// Reads at most `DEFAULT_MAX_BYTES`; use `open_bounded` for another input budget.
pub fn open(path: &Path, kind: ArtifactKind) -> Result<Artifact, Error> {
    open_bounded(path, kind, DEFAULT_MAX_BYTES)
}
pub fn open_bounded(path: &Path, kind: ArtifactKind, maximum: u64) -> Result<Artifact, Error> {
    let mut file = File::open(path)?;
    let length = checked_file_length(&file, maximum)?;
    let mut header = [0; HEADER_BYTES];
    file.read_exact(&mut header)?;
    directory_bounds(&header, kind, length)?;
    file.seek(SeekFrom::Start(0))?;
    let mut bytes = Vec::new();
    bytes.try_reserve_exact(length).map_err(|_| Error::Limit {
        size: length as u64,
        maximum,
    })?;
    bytes.resize(length, 0);
    file.read_exact(&mut bytes)?;
    let mut extra = [0];
    if file.read(&mut extra)? != 0 {
        return Err(Error::Format("file grew during admission"));
    }
    admit(Storage::Owned(bytes), kind)
}

/// Maps a backing file without copying its content.
///
/// # Safety
/// The caller must keep every byte of this file immutable and keep its length
/// unchanged until the returned artifact is dropped. This includes all other
/// processes and file descriptors. Never truncate or overwrite a published file;
/// unlinking on Unix is permitted because this owner retains the open descriptor.
/// Permissions, checksums and cooperative locks do not alone establish this.
#[cfg(unix)]
pub unsafe fn open_mapped_immutable(
    path: &Path,
    kind: ArtifactKind,
    maximum: u64,
) -> Result<Artifact, Error> {
    let file = File::open(path)?;
    let length = checked_file_length(&file, maximum)?;
    // SAFETY: the caller provides the backing-file lifetime contract above.
    let mapping = unsafe { mapping::Mapping::new(file, length)? };
    admit(Storage::Mapped(mapping), kind)
}

fn checked_file_length(file: &File, maximum: u64) -> Result<usize, Error> {
    let size = file.metadata()?.len();
    if size > maximum || size > isize::MAX as u64 {
        return Err(Error::Limit {
            size,
            maximum: maximum.min(isize::MAX as u64),
        });
    }
    if size < HEADER_BYTES as u64 {
        return Err(Error::Format("truncated header"));
    }
    Ok(size as usize)
}

fn read_u32(bytes: &[u8], offset: usize) -> u32 {
    u32::from_le_bytes(bytes[offset..offset + 4].try_into().unwrap())
}
fn read_u64(bytes: &[u8], offset: usize) -> u64 {
    u64::from_le_bytes(bytes[offset..offset + 8].try_into().unwrap())
}
fn align8(value: usize) -> Result<usize, Error> {
    value
        .checked_add(7)
        .map(|value| value & !7)
        .ok_or(Error::Format("length overflow"))
}
fn as_usize(value: u64) -> Result<usize, Error> {
    usize::try_from(value).map_err(|_| Error::Format("length does not fit address space"))
}
fn artifact_checksum(bytes: &[u8]) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(&bytes[..CHECKSUM_START]);
    hash.update([0; 32]);
    hash.update(&bytes[CHECKSUM_END..]);
    hash.finalize().into()
}
/// Validate the fixed header before allocating a directory or full-file buffer.
/// Both owned and streaming admission use this exact structural contract.
fn directory_bounds(
    header: &[u8],
    kind: ArtifactKind,
    length: usize,
) -> Result<(usize, usize), Error> {
    if header.len() < HEADER_BYTES {
        return Err(Error::Format("truncated header"));
    }
    if &header[..8] != MAGIC {
        return Err(Error::Format("magic"));
    }
    if read_u32(header, 8) != VERSION {
        return Err(Error::Format("unsupported version"));
    }
    let actual = read_u32(header, 12);
    if actual != kind as u32 {
        return Err(Error::Kind {
            expected: kind,
            actual,
        });
    }
    let count = read_u32(header, 16) as usize;
    if count > MAX_SECTIONS {
        return Err(Error::Format("section directory limit"));
    }
    if read_u32(header, 20) != SECTION_BYTES as u32 {
        return Err(Error::Format("section directory entry size"));
    }
    let header_end = as_usize(read_u64(header, 24))?;
    let directory_end = HEADER_BYTES
        .checked_add(
            count
                .checked_mul(SECTION_BYTES)
                .ok_or(Error::Format("section directory overflow"))?,
        )
        .ok_or(Error::Format("section directory overflow"))?;
    if header_end != align8(directory_end)? || header_end > length {
        return Err(Error::Format("section directory bounds"));
    }
    if read_u64(header, 32) != length as u64 {
        return Err(Error::Format("file length"));
    }
    if header[72..80].iter().any(|&byte| byte != 0) {
        return Err(Error::Format("reserved header bits"));
    }
    Ok((count, header_end))
}

fn parse_directory(
    header: &[u8],
    directory: &[u8],
    kind: ArtifactKind,
    length: usize,
) -> Result<Vec<SectionMeta>, Error> {
    let (count, header_end) = directory_bounds(header, kind, length)?;
    if directory.len() != header_end - HEADER_BYTES {
        return Err(Error::Format("section directory bounds"));
    }
    let mut sections = Vec::new();
    sections
        .try_reserve_exact(count)
        .map_err(|_| Error::Format("cannot reserve section directory"))?;
    let mut previous_id = None;
    let mut previous_end = header_end;
    for index in 0..count {
        let start = index * SECTION_BYTES;
        let id = read_u32(directory, start);
        if previous_id.is_some_and(|previous| previous >= id) {
            return Err(Error::Format("section IDs must be unique and sorted"));
        }
        if read_u32(directory, start + 4) != 0 {
            return Err(Error::Format("reserved section flags"));
        }
        let offset = as_usize(read_u64(directory, start + 16))?;
        let section_length = as_usize(read_u64(directory, start + 24))?;
        let end = offset
            .checked_add(section_length)
            .ok_or(Error::Format("section length overflow"))?;
        if offset % 8 != 0 || offset < previous_end || end > length {
            return Err(Error::Format("section bounds, alignment or overlap"));
        }
        sections.push(SectionMeta {
            id,
            count: read_u64(directory, start + 8),
            offset,
            length: section_length,
            checksum: directory[start + 32..start + 64].try_into().unwrap(),
        });
        previous_id = Some(id);
        previous_end = end;
    }
    if previous_end != length {
        return Err(Error::Format("unclaimed trailing data"));
    }
    Ok(sections)
}

fn admit(storage: Storage, kind: ArtifactKind) -> Result<Artifact, Error> {
    let bytes = storage.bytes();
    let (_, header_end) = directory_bounds(bytes, kind, bytes.len())?;
    let sections = parse_directory(
        &bytes[..HEADER_BYTES],
        &bytes[HEADER_BYTES..header_end],
        kind,
        bytes.len(),
    )?;
    let identity: [u8; 32] = bytes[CHECKSUM_START..CHECKSUM_END].try_into().unwrap();
    let mut previous_end = header_end;
    for section in &sections {
        if bytes[previous_end..section.offset]
            .iter()
            .any(|&byte| byte != 0)
        {
            return Err(Error::Format("nonzero section padding"));
        }
        let end = section.offset + section.length;
        let checksum: [u8; 32] = Sha256::digest(&bytes[section.offset..end]).into();
        if checksum != section.checksum {
            return Err(Error::Checksum {
                section: Some(section.id),
            });
        }
        previous_end = end;
    }
    if artifact_checksum(bytes) != identity {
        return Err(Error::Checksum { section: None });
    }
    Ok(Artifact {
        storage,
        identity,
        kind,
        sections,
    })
}

/// A fully checked artifact identity, without retaining its content in memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VerifiedArtifact {
    pub identity: [u8; 32],
    pub kind: ArtifactKind,
    pub byte_len: u64,
}

/// Verify header, directory, padding, every section digest and the complete file
/// digest with bounded scratch. This is safe for ordinary mutable/untrusted paths;
/// no references to their bytes survive. Consumers still re-admit on later reads.
/// Memory use is bounded by MAX_SECTIONS directory entries and a 64 KiB buffer.
pub fn verify_file(
    path: &Path,
    kind: ArtifactKind,
    maximum: u64,
) -> Result<VerifiedArtifact, Error> {
    let mut file = File::open(path)?;
    let length = checked_file_length(&file, maximum)?;
    let mut header = [0; HEADER_BYTES];
    file.read_exact(&mut header)?;
    let (_, header_end) = directory_bounds(&header, kind, length)?;
    let directory_length = header_end - HEADER_BYTES;
    let mut directory = Vec::new();
    directory
        .try_reserve_exact(directory_length)
        .map_err(|_| Error::Format("cannot reserve section directory"))?;
    directory.resize(directory_length, 0);
    file.read_exact(&mut directory)?;
    let sections = parse_directory(&header, &directory, kind, length)?;
    let identity: [u8; 32] = header[CHECKSUM_START..CHECKSUM_END].try_into().unwrap();
    header[CHECKSUM_START..CHECKSUM_END].fill(0);
    let mut aggregate = Sha256::new();
    aggregate.update(header);
    aggregate.update(&directory);
    let mut buffer = [0; 64 * 1024];
    let mut position = header_end;
    for section in &sections {
        let mut padding = section.offset - position;
        while padding != 0 {
            let n = padding.min(buffer.len());
            file.read_exact(&mut buffer[..n])?;
            if buffer[..n].iter().any(|&byte| byte != 0) {
                return Err(Error::Format("nonzero section padding"));
            }
            aggregate.update(&buffer[..n]);
            padding -= n;
        }
        let mut checksum = Sha256::new();
        let mut remaining = section.length;
        while remaining != 0 {
            let n = remaining.min(buffer.len());
            file.read_exact(&mut buffer[..n])?;
            aggregate.update(&buffer[..n]);
            checksum.update(&buffer[..n]);
            remaining -= n;
        }
        let checksum: [u8; 32] = checksum.finalize().into();
        if checksum != section.checksum {
            return Err(Error::Checksum {
                section: Some(section.id),
            });
        }
        position = section.offset + section.length;
    }
    let mut extra = [0];
    if file.read(&mut extra)? != 0 {
        return Err(Error::Format("file grew during admission"));
    }
    let actual: [u8; 32] = aggregate.finalize().into();
    if actual != identity {
        return Err(Error::Checksum { section: None });
    }
    Ok(VerifiedArtifact {
        identity,
        kind,
        byte_len: length as u64,
    })
}

/// Stream an artifact, sync its bytes, then atomically publish without replacing
/// any existing inode. Identical repeated publication is idempotent. A crash can
/// leave an unreferenced temporary file, never a partially published destination.
pub fn write(path: &Path, kind: ArtifactKind, sections: &[Section<'_>]) -> Result<[u8; 32], Error> {
    let (header, ordered, total) = make_header(kind, sections)?;
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent)?;
    let (temporary, file) = create_temporary(parent)?;
    let cleanup = Temporary(temporary);
    let mut output = BufWriter::with_capacity(128 * 1024, file);
    let mut hasher = Sha256::new();
    output.write_all(&header)?;
    hasher.update(&header);
    let mut position = header.len();
    for &index in &ordered {
        let aligned = align8(position)?;
        let padding = [0; 8];
        output.write_all(&padding[..aligned - position])?;
        hasher.update(&padding[..aligned - position]);
        output.write_all(sections[index].bytes)?;
        hasher.update(sections[index].bytes);
        position = aligned + sections[index].bytes.len();
    }
    debug_assert_eq!(position, total);
    let identity: [u8; 32] = hasher.finalize().into();
    output.flush()?;
    let mut file = output
        .into_inner()
        .map_err(|error| Error::Io(error.into_error()))?;
    file.seek(SeekFrom::Start(CHECKSUM_START as u64))?;
    file.write_all(&identity)?;
    let mut permissions = file.metadata()?.permissions();
    permissions.set_readonly(true);
    file.set_permissions(permissions)?;
    file.sync_all()?;
    match fs::hard_link(&cleanup.0, path) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            // Bounded streaming validation avoids loading an existing full graph.
            if checksum_file(path, kind, total as u64)? != identity {
                return Err(Error::Conflict(path.to_path_buf()));
            }
        }
        Err(error) => return Err(error.into()),
    }
    sync_directory(parent)?;
    Ok(identity)
}

/// Publish under its content identity. Only catalogue references need mutation.
pub fn publish(
    directory: &Path,
    kind: ArtifactKind,
    sections: &[Section<'_>],
) -> Result<PublishedArtifact, Error> {
    fs::create_dir_all(directory)?;
    let (staging, file) = create_temporary(directory)?;
    drop(file);
    fs::remove_file(&staging)?;
    let staging_cleanup = Temporary(staging);
    let identity = write(&staging_cleanup.0, kind, sections)?;
    let path = directory.join(format!("{}.rsel", identity_hex(&identity)));
    match fs::hard_link(&staging_cleanup.0, &path) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            if checksum_file(&path, kind, fs::metadata(&staging_cleanup.0)?.len())? != identity {
                return Err(Error::Conflict(path));
            }
        }
        Err(error) => return Err(error.into()),
    }
    sync_directory(directory)?;
    Ok(PublishedArtifact { identity, path })
}
#[derive(Debug, Clone)]
pub struct PublishedArtifact {
    pub identity: [u8; 32],
    pub path: PathBuf,
}

fn make_header(
    kind: ArtifactKind,
    sections: &[Section<'_>],
) -> Result<(Vec<u8>, Vec<usize>, usize), Error> {
    if sections.len() > MAX_SECTIONS {
        return Err(Error::Format("section directory limit"));
    }
    let count = u32::try_from(sections.len()).map_err(|_| Error::Format("too many sections"))?;
    let header_length = align8(
        HEADER_BYTES
            .checked_add(
                sections
                    .len()
                    .checked_mul(SECTION_BYTES)
                    .ok_or(Error::Format("section directory overflow"))?,
            )
            .ok_or(Error::Format("section directory overflow"))?,
    )?;
    let mut header = Vec::new();
    header
        .try_reserve_exact(header_length)
        .map_err(|_| Error::Format("cannot reserve section directory"))?;
    header.resize(header_length, 0);
    header[..8].copy_from_slice(MAGIC);
    header[8..12].copy_from_slice(&VERSION.to_le_bytes());
    header[12..16].copy_from_slice(&(kind as u32).to_le_bytes());
    header[16..20].copy_from_slice(&count.to_le_bytes());
    header[20..24].copy_from_slice(&(SECTION_BYTES as u32).to_le_bytes());
    header[24..32].copy_from_slice(&(header_length as u64).to_le_bytes());
    let mut ordered: Vec<usize> = (0..sections.len()).collect();
    ordered.sort_unstable_by_key(|&index| sections[index].id);
    let mut previous_id = None;
    let mut total = header_length;
    for (entry, &index) in ordered.iter().enumerate() {
        let section = &sections[index];
        if previous_id == Some(section.id) {
            return Err(Error::Format("duplicate section ID"));
        }
        total = align8(total)?;
        let start = HEADER_BYTES + entry * SECTION_BYTES;
        header[start..start + 4].copy_from_slice(&section.id.to_le_bytes());
        header[start + 8..start + 16].copy_from_slice(&section.count.to_le_bytes());
        header[start + 16..start + 24].copy_from_slice(&(total as u64).to_le_bytes());
        header[start + 24..start + 32].copy_from_slice(&(section.bytes.len() as u64).to_le_bytes());
        header[start + 32..start + 64].copy_from_slice(&Sha256::digest(section.bytes));
        total = total
            .checked_add(section.bytes.len())
            .ok_or(Error::Format("artifact length overflow"))?;
        previous_id = Some(section.id);
    }
    header[32..40].copy_from_slice(&(total as u64).to_le_bytes());
    Ok((header, ordered, total))
}
fn checksum_file(path: &Path, kind: ArtifactKind, expected_length: u64) -> Result<[u8; 32], Error> {
    let mut file = File::open(path)?;
    if file.metadata()?.len() != expected_length {
        return Err(Error::Conflict(path.to_path_buf()));
    }
    let mut header = [0; HEADER_BYTES];
    file.read_exact(&mut header)?;
    if &header[..8] != MAGIC || read_u32(&header, 12) != kind as u32 {
        return Err(Error::Conflict(path.to_path_buf()));
    }
    let stored: [u8; 32] = header[CHECKSUM_START..CHECKSUM_END].try_into().unwrap();
    header[CHECKSUM_START..CHECKSUM_END].fill(0);
    let mut hash = Sha256::new();
    hash.update(header);
    let mut buffer = [0; 64 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hash.update(&buffer[..read]);
    }
    let actual: [u8; 32] = hash.finalize().into();
    if actual != stored {
        return Err(Error::Checksum { section: None });
    }
    Ok(actual)
}
struct Temporary(PathBuf);
impl Drop for Temporary {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}
fn create_temporary(directory: &Path) -> Result<(PathBuf, File), Error> {
    loop {
        let name = format!(
            ".rsel-{}-{}.tmp",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed)
        );
        let path = directory.join(name);
        match OpenOptions::new().write(true).create_new(true).open(&path) {
            Ok(file) => return Ok((path, file)),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error.into()),
        }
    }
}
fn sync_directory(directory: &Path) -> Result<(), Error> {
    #[cfg(unix)]
    File::open(directory)?.sync_all()?;
    #[cfg(not(unix))]
    let _ = directory; // Directory fsync is not exposed portably by std.
    Ok(())
}

#[cfg(unix)]
mod mapping {
    use super::*;
    use std::os::fd::AsRawFd;
    use std::ptr::NonNull;
    pub(super) struct Mapping {
        pointer: NonNull<u8>,
        length: usize,
        _file: File,
    }
    impl Mapping {
        pub(super) unsafe fn new(file: File, length: usize) -> Result<Self, Error> {
            // SAFETY: length was checked nonzero/addressable, fd is live and the
            // caller promises immutable bytes for the returned mapping lifetime.
            let pointer = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    length,
                    libc::PROT_READ,
                    libc::MAP_PRIVATE,
                    file.as_raw_fd(),
                    0,
                )
            };
            if pointer == libc::MAP_FAILED {
                return Err(io::Error::last_os_error().into());
            }
            let pointer =
                NonNull::new(pointer.cast()).ok_or(Error::Format("null mapping address"))?;
            Ok(Self {
                pointer,
                length,
                _file: file,
            })
        }
        pub(super) fn bytes(&self) -> &[u8] {
            // SAFETY: mapping owns a live immutable region until Drop, and length
            // was bounded by isize::MAX. Returned references borrow this owner.
            unsafe { std::slice::from_raw_parts(self.pointer.as_ptr(), self.length) }
        }
    }
    // SAFETY: backing bytes are immutable under Mapping::new's caller contract.
    unsafe impl Send for Mapping {}
    unsafe impl Sync for Mapping {}
    impl Drop for Mapping {
        fn drop(&mut self) {
            // SAFETY: this owner unmaps precisely its own successful mapping.
            unsafe {
                libc::munmap(self.pointer.as_ptr().cast(), self.length);
            }
        }
    }
}

/// Fixed-size section description for an encoder that need not stage its output.
#[derive(Debug, Clone, Copy)]
pub struct StreamingSection {
    pub id: u32,
    pub count: u64,
    pub length: u64,
}

/// Encode twice without holding a second snapshot-sized buffer. The first pass
/// computes section digests; the second streams directly into a temporary file.
/// The encoder must produce identical bytes on both invocations for each ID.
pub fn write_streaming(
    path: &Path,
    kind: ArtifactKind,
    sections: &[StreamingSection],
    mut emit: impl FnMut(u32, &mut dyn Write) -> io::Result<()>,
) -> Result<[u8; 32], Error> {
    if sections.len() > MAX_SECTIONS {
        return Err(Error::Format("section directory limit"));
    }
    let count = u32::try_from(sections.len()).map_err(|_| Error::Format("too many sections"))?;
    let header_length = align8(
        HEADER_BYTES
            .checked_add(
                sections
                    .len()
                    .checked_mul(SECTION_BYTES)
                    .ok_or(Error::Format("section directory overflow"))?,
            )
            .ok_or(Error::Format("section directory overflow"))?,
    )?;
    let mut header = Vec::new();
    header
        .try_reserve_exact(header_length)
        .map_err(|_| Error::Format("cannot reserve section directory"))?;
    header.resize(header_length, 0);
    header[..8].copy_from_slice(MAGIC);
    header[8..12].copy_from_slice(&VERSION.to_le_bytes());
    header[12..16].copy_from_slice(&(kind as u32).to_le_bytes());
    header[16..20].copy_from_slice(&count.to_le_bytes());
    header[20..24].copy_from_slice(&(SECTION_BYTES as u32).to_le_bytes());
    header[24..32].copy_from_slice(&(header_length as u64).to_le_bytes());
    let mut ordered: Vec<usize> = (0..sections.len()).collect();
    ordered.sort_unstable_by_key(|&index| sections[index].id);
    let mut previous_id = None;
    let mut total = header_length;
    for (entry, &index) in ordered.iter().enumerate() {
        let section = sections[index];
        if previous_id == Some(section.id) {
            return Err(Error::Format("duplicate section ID"));
        }
        let length = as_usize(section.length)?;
        total = align8(total)?;
        let start = HEADER_BYTES + entry * SECTION_BYTES;
        header[start..start + 4].copy_from_slice(&section.id.to_le_bytes());
        header[start + 8..start + 16].copy_from_slice(&section.count.to_le_bytes());
        header[start + 16..start + 24].copy_from_slice(&(total as u64).to_le_bytes());
        header[start + 24..start + 32].copy_from_slice(&section.length.to_le_bytes());
        let mut sink = HashWriter {
            hash: Sha256::new(),
            count: 0,
            maximum: section.length,
            aggregate: None,
            output: None,
            buffer: [0; 16 * 1024],
            buffered: 0,
        };
        emit(section.id, &mut sink)?;
        sink.flush_pending()?;
        if sink.count != section.length {
            return Err(Error::Format("encoder emitted a different section length"));
        }
        header[start + 32..start + 64].copy_from_slice(&sink.hash.finalize());
        total = total
            .checked_add(length)
            .ok_or(Error::Format("artifact length overflow"))?;
        previous_id = Some(section.id);
    }
    header[32..40].copy_from_slice(&(total as u64).to_le_bytes());
    let parent = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    fs::create_dir_all(parent)?;
    let (temporary, file) = create_temporary(parent)?;
    let cleanup = Temporary(temporary);
    let mut output = BufWriter::with_capacity(128 * 1024, file);
    output.write_all(&header)?;
    let mut aggregate = Sha256::new();
    aggregate.update(&header);
    let mut position = header.len();
    for (entry, &index) in ordered.iter().enumerate() {
        let aligned = align8(position)?;
        output.write_all(&[0; 8][..aligned - position])?;
        aggregate.update(&[0; 8][..aligned - position]);
        let section = sections[index];
        let mut sink = HashWriter {
            hash: Sha256::new(),
            count: 0,
            maximum: section.length,
            aggregate: Some(&mut aggregate),
            output: Some(&mut output),
            buffer: [0; 16 * 1024],
            buffered: 0,
        };
        emit(section.id, &mut sink)?;
        sink.flush_pending()?;
        if sink.count != section.length {
            return Err(Error::Format("encoder emitted a different section length"));
        }
        let actual: [u8; 32] = sink.hash.finalize().into();
        let start = HEADER_BYTES + entry * SECTION_BYTES;
        if actual[..] != header[start + 32..start + 64] {
            return Err(Error::Format("encoder output changed between passes"));
        }
        position = aligned + as_usize(section.length)?;
    }
    debug_assert_eq!(position, total);
    output.flush()?;
    let mut file = output
        .into_inner()
        .map_err(|error| Error::Io(error.into_error()))?;
    let identity: [u8; 32] = aggregate.finalize().into();
    file.seek(SeekFrom::Start(CHECKSUM_START as u64))?;
    file.write_all(&identity)?;
    let mut permissions = file.metadata()?.permissions();
    permissions.set_readonly(true);
    file.set_permissions(permissions)?;
    file.sync_all()?;
    match fs::hard_link(&cleanup.0, path) {
        Ok(()) => {}
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            if checksum_file(path, kind, total as u64)? != identity {
                return Err(Error::Conflict(path.to_path_buf()));
            }
        }
        Err(error) => return Err(error.into()),
    }
    sync_directory(parent)?;
    Ok(identity)
}
struct HashWriter<'a> {
    hash: Sha256,
    count: u64,
    maximum: u64,
    aggregate: Option<&'a mut Sha256>,
    output: Option<&'a mut dyn Write>,
    buffer: [u8; 16 * 1024],
    buffered: usize,
}
impl HashWriter<'_> {
    fn flush_pending(&mut self) -> io::Result<()> {
        let bytes = &self.buffer[..self.buffered];
        if let Some(output) = &mut self.output {
            output.write_all(bytes)?;
        }
        self.hash.update(bytes);
        if let Some(aggregate) = &mut self.aggregate {
            aggregate.update(bytes);
        }
        self.buffered = 0;
        Ok(())
    }
}
impl Write for HashWriter<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let count = self
            .count
            .checked_add(bytes.len() as u64)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "encoder length overflow"))?;
        if count > self.maximum {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "encoder exceeded section length",
            ));
        }
        let mut remaining = bytes;
        while !remaining.is_empty() {
            // Large encoder chunks bypass the copy; small scalar/record writes
            // amortize hashing and I/O over this bounded stack buffer.
            if self.buffered == 0 && remaining.len() >= self.buffer.len() {
                if let Some(output) = &mut self.output {
                    output.write_all(remaining)?;
                }
                self.hash.update(remaining);
                if let Some(aggregate) = &mut self.aggregate {
                    aggregate.update(remaining);
                }
                remaining = &[];
            } else {
                let take = remaining.len().min(self.buffer.len() - self.buffered);
                self.buffer[self.buffered..self.buffered + take]
                    .copy_from_slice(&remaining[..take]);
                self.buffered += take;
                remaining = &remaining[take..];
                if self.buffered == self.buffer.len() {
                    self.flush_pending()?;
                }
            }
        }
        self.count = count;
        Ok(bytes.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        self.flush_pending()?;
        if let Some(output) = &mut self.output {
            output.flush()?;
        }
        Ok(())
    }
}
