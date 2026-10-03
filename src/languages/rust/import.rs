//! Refresh runs the pinned exporter; ordinary loading only checks locked inputs.
use super::schema::{COMPILER_COMMIT, RustExport, SCHEMA, TARGET};
use crate::languages::compiler_process::{CompilerLimits, run_compiler};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

#[derive(Clone, Debug)]
pub struct PreparedRustImport {
    inner: Arc<Inner>,
}
#[derive(Debug)]
struct Inner {
    export: RustExport,
    identity: String,
}
impl PreparedRustImport {
    pub fn logical_source(&self) -> &str {
        &self.inner.export.logical_source
    }
    pub fn identity(&self) -> &str {
        &self.inner.identity
    }
    pub fn export(&self) -> &RustExport {
        &self.inner.export
    }
}
#[cfg(test)]
pub(super) fn prepared_for_test(export: RustExport) -> Result<PreparedRustImport, String> {
    super::lowering::lower(&export)?;
    Ok(PreparedRustImport {
        inner: Arc::new(Inner {
            export,
            identity: "charon-authority-test".into(),
        }),
    })
}
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    schema: u32,
    language: String,
    target: String,
    source: String,
    exporter: String,
    artifact: String,
    #[serde(default)]
    backend: Option<String>,
}
#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Lock {
    schema: u32,
    config: String,
    source: String,
    exporter: String,
    artifact: String,
    identity: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    charon_driver: Option<String>,
}
fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
fn identity(config: &str, source: &str, exporter: &str, artifact: &str) -> String {
    digest(format!("click-rust-import-v2\n{config}\n{source}\n{exporter}\n{artifact}\n{COMPILER_COMMIT}\n{TARGET}").as_bytes())
}
fn import_identity(
    c: &Config,
    config: &str,
    source: &str,
    exporter: &str,
    artifact: &str,
    driver: &Option<String>,
) -> String {
    match driver {
        Some(driver) if c.backend.as_deref() == Some("charon-trial") => digest(format!("click-charon-trial-v1\n{config}\n{source}\n{exporter}\n{artifact}\n{driver}\n{}\n{}\nflat-record-drop-v1\nunsigned-from-v1\ncompact-uniform-scalar-array-v1\nbyte-slice-metadata-v1\nshared-byte-chunks-exact-v1\nnested-natural-while-v1\nbyte-array-unsize-v1\nunsigned-checksum-operators-v1\nborrowed-scalar-array-fields-v1", super::charon::COMMIT, super::charon::COMPILER).as_bytes()),
        _ => identity(config, source, exporter, artifact),
    }
}
fn read(path: &Path, limit: usize) -> Result<Vec<u8>, String> {
    if !fs::symlink_metadata(path)
        .map_err(|e| format!("read `{}`: {e}", path.display()))?
        .file_type()
        .is_file()
    {
        return Err(format!("`{}` must be a regular file", path.display()));
    }
    let f = fs::File::open(path).map_err(|e| e.to_string())?;
    if !f.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err("Rust input changed file type".into());
    }
    let mut bytes = Vec::new();
    f.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > limit {
        return Err(format!(
            "`{}` exceeds its {limit}-byte limit",
            path.display()
        ));
    }
    Ok(bytes)
}
fn local_file(root: &Path, name: &str) -> Result<PathBuf, String> {
    let path = Path::new(name);
    if path.components().count() != 1
        || !matches!(path.components().next(), Some(Component::Normal(_)))
    {
        return Err("Rust source/artifact must name files in the import directory".into());
    }
    Ok(root.join(path))
}
fn config(path: &Path) -> Result<(Config, Vec<u8>, PathBuf), String> {
    let bytes = read(path, 1 << 20)?;
    let c: Config =
        serde_json::from_slice(&bytes).map_err(|e| format!("Rust import config: {e}"))?;
    // Configuration version is independent of the typed artifact schema.
    if !matches!(
        (c.schema, c.backend.as_deref()),
        (2, None) | (3, Some("charon-trial"))
    ) || c.language != "rust"
        || c.target != TARGET
    {
        return Err("unsupported Rust import schema/language/target".into());
    }
    let absolute = fs::canonicalize(path).map_err(|e| e.to_string())?;
    let root = absolute
        .parent()
        .ok_or("Rust config needs a directory")?
        .to_path_buf();
    local_file(&root, &c.source)?;
    local_file(&root, &c.artifact)?;
    if !c.source.ends_with(".rs")
        || c.source == c.artifact
        || c.artifact == absolute.file_name().unwrap().to_string_lossy()
        || c.artifact == format!("{}.lock", absolute.file_name().unwrap().to_string_lossy())
    {
        return Err("Rust artifact output must differ from source/config/lock".into());
    }
    Ok((c, bytes, root))
}
fn lock_path(path: &Path) -> Result<PathBuf, String> {
    let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .ok_or("invalid Rust config name")?;
    Ok(path.with_file_name(format!("{name}.lock")))
}
fn decode(bytes: &[u8], c: &Config, source: &[u8]) -> Result<RustExport, String> {
    if c.backend.as_deref() == Some("charon-trial") {
        let export = super::charon::decode(bytes, &c.source, source)?;
        super::lowering::lower(&export)?;
        return Ok(export);
    }
    let export: RustExport =
        serde_json::from_slice(bytes).map_err(|e| format!("Rust semantic artifact: {e}"))?;
    if export.schema != SCHEMA
        || export.compiler_commit != COMPILER_COMMIT
        || export.target != TARGET
        || export.edition != "2024"
        || !export.overflow_checks
        || export.panic != "abort"
        || export.mir_opt_level != 0
        || export.logical_source != c.source
    {
        return Err("Rust artifact differs from the supported compiler profile".into());
    }
    super::lowering::lower(&export)?;
    Ok(export)
}
fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    match fs::symlink_metadata(path) {
        Ok(m) if !m.file_type().is_file() => {
            return Err("Rust output must be a regular file".into());
        }
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => return Err(e.to_string()),
        _ => {}
    }
    let temp = path.with_file_name(format!(
        ".click-rust-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let result = (|| {
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp)
            .map_err(|e| e.to_string())?;
        f.write_all(bytes).map_err(|e| e.to_string())?;
        f.sync_all().map_err(|e| e.to_string())?;
        fs::rename(&temp, path).map_err(|e| e.to_string())
    })();
    let _ = fs::remove_file(temp);
    result
}
pub fn refresh_import(path: &Path) -> Result<(), String> {
    let (c, bytes, root) = config(path)?;
    let source = local_file(&root, &c.source)?;
    let source_bytes = read(&source, 1 << 20)?;
    let exporter =
        fs::canonicalize(root.join(&c.exporter)).map_err(|e| format!("Rust exporter: {e}"))?;
    let artifact_path = local_file(&root, &c.artifact)?;
    let lock_name = lock_path(path)?;
    let lock_output = root.join(lock_name.file_name().ok_or("invalid Rust lock filename")?);
    if exporter == artifact_path
        || exporter == lock_output
        || exporter == source
        || exporter == fs::canonicalize(path).map_err(|e| e.to_string())?
    {
        return Err("Rust exporter must differ from source/config/artifact/lock".into());
    }
    let exporter_bytes = read(&exporter, 128 << 20)?;
    let mut driver_hash = None;
    let output_bytes = if c.backend.as_deref() == Some("charon-trial") {
        let driver = exporter.with_file_name("charon-driver");
        if driver == artifact_path || driver == lock_output {
            return Err("Charon driver must differ from artifact/lock outputs".into());
        }
        let driver_bytes = read(&driver, 128 << 20)?;
        driver_hash = Some(digest(&driver_bytes));
        let output = super::charon::extract(&exporter, &source, &root)?;
        if driver_bytes != read(&driver, 128 << 20)? {
            return Err("Charon driver changed during extraction".into());
        }
        output
    } else {
        run_compiler(
            &exporter,
            &[source.to_string_lossy().into_owned(), c.source.clone()],
            &root,
            &BTreeMap::new(),
            CompilerLimits {
                timeout: Duration::from_secs(30),
                max_stdout_bytes: 4 << 20,
                max_stderr_bytes: 64 << 10,
            },
        )?
        .stdout
    };
    decode(&output_bytes, &c, &source_bytes)?;
    if bytes != read(path, 1 << 20)?
        || source_bytes != read(&source, 1 << 20)?
        || exporter_bytes != read(&exporter, 128 << 20)?
    {
        return Err("Rust inputs changed during compiler extraction".into());
    }
    let config_hash = digest(&bytes);
    let source_hash = digest(&source_bytes);
    let exporter_hash = digest(&exporter_bytes);
    let artifact_hash = digest(&output_bytes);
    let lock = Lock {
        schema: SCHEMA,
        identity: import_identity(
            &c,
            &config_hash,
            &source_hash,
            &exporter_hash,
            &artifact_hash,
            &driver_hash,
        ),
        charon_driver: driver_hash,
        config: config_hash,
        source: source_hash,
        exporter: exporter_hash,
        artifact: artifact_hash,
    };
    write_atomic(&local_file(&root, &c.artifact)?, &output_bytes)?;
    write_atomic(
        &lock_path(path)?,
        &serde_json::to_vec_pretty(&lock).map_err(|e| e.to_string())?,
    )
}
pub fn load_import(path: &Path) -> Result<PreparedRustImport, String> {
    let (c, bytes, root) = config(path)?;
    let lock: Lock =
        serde_json::from_slice(&read(&lock_path(path)?, 1 << 20)?).map_err(|e| e.to_string())?;
    let artifact = read(&local_file(&root, &c.artifact)?, 4 << 20)?;
    let source = read(&local_file(&root, &c.source)?, 1 << 20)?;
    if lock.schema != SCHEMA
        || lock.config != digest(&bytes)
        || lock.source != digest(&source)
        || lock.artifact != digest(&artifact)
        || lock.charon_driver.is_some() != (c.backend.as_deref() == Some("charon-trial"))
        || lock.identity
            != import_identity(
                &c,
                &lock.config,
                &lock.source,
                &lock.exporter,
                &lock.artifact,
                &lock.charon_driver,
            )
    {
        return Err("Rust import lock differs from its inputs; refresh it".into());
    }
    let export = decode(&artifact, &c, &source)?;
    Ok(PreparedRustImport {
        inner: Arc::new(Inner {
            export,
            identity: lock.identity,
        }),
    })
}
