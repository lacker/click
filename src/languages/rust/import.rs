//! Refresh runs the pinned exporter; ordinary loading only checks locked inputs.
use super::schema::{RustExport, SCHEMA, TARGET};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::Read;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct PreparedRustImport {
    inner: Arc<Inner>,
}
#[derive(Debug)]
struct Inner {
    export: RustExport,
    identity: String,
    execution: crate::languages::ExecutionCache,
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
    pub(crate) fn prepared_execution(
        &self,
    ) -> Result<Arc<crate::languages::PreparedExecution>, String> {
        self.inner
            .execution
            .get_or_lower(|| super::prepare_execution(self))
    }
}
#[cfg(test)]
pub(super) fn prepared_for_test(export: RustExport) -> Result<PreparedRustImport, String> {
    super::lowering::lower(&export)?;
    Ok(PreparedRustImport {
        inner: Arc::new(Inner {
            export,
            identity: "charon-authority-test".into(),
            execution: Default::default(),
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
    #[serde(default, rename = "crate")]
    crate_config: Option<super::crate_inputs::CrateConfig>,
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
fn import_identity(
    config: &str,
    source: &str,
    exporter: &str,
    artifact: &str,
    driver: &str,
) -> String {
    let profile = super::profile::get();
    digest(
        format!(
            "{}\n{config}\n{source}\n{exporter}\n{artifact}\n{driver}\n{}",
            profile.identity,
            profile.semantic_identity()
        )
        .as_bytes(),
    )
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
        (3 | 4, None | Some("charon") | Some("charon-trial"))
    ) || c.language != "rust"
        || c.target != TARGET
    {
        return Err("unsupported Rust import schema/language/target; use schema 3 and native Charon .ullbc artifacts (legacy extraction is retired)".into());
    }
    let absolute = fs::canonicalize(path).map_err(|e| e.to_string())?;
    let root = absolute
        .parent()
        .ok_or("Rust config needs a directory")?
        .to_path_buf();
    match (c.schema, &c.crate_config) {
        (3, None) => {
            local_file(&root, &c.source)?;
        }
        (4, Some(config)) => {
            config.validate(&c.source)?;
            for name in &config.files {
                super::crate_inputs::file(&root, name)?;
                if name == &c.artifact
                    || name == absolute.file_name().unwrap().to_string_lossy().as_ref()
                    || name == &format!("{}.lock", absolute.file_name().unwrap().to_string_lossy())
                {
                    return Err(
                        "Rust crate inputs must differ from config/artifact/lock outputs".into(),
                    );
                }
            }
        }
        _ => {
            return Err(
                "Rust schema 4 requires a crate configuration; schema 3 is single-file".into(),
            );
        }
    }
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
fn sources(c: &Config, root: &Path) -> Result<super::crate_inputs::SourceFiles, String> {
    let names = c
        .crate_config
        .as_ref()
        .map_or_else(|| vec![c.source.clone()], |c| c.files.clone());
    let mut files = std::collections::BTreeMap::new();
    let mut total = 0;
    for name in names {
        let path = if c.crate_config.is_some() {
            super::crate_inputs::file(root, &name)?
        } else {
            local_file(root, &name)?
        };
        let bytes = read(&path, 1 << 20)?;
        total += bytes.len();
        if total > 4 << 20 {
            return Err("Rust crate source closure exceeds its byte bound".into());
        }
        files.insert(name, bytes);
    }
    Ok(files)
}
fn source_digest(c: &Config, files: &super::crate_inputs::SourceFiles) -> String {
    if c.crate_config.is_none() {
        return digest(&files[&c.source]);
    }
    let hashes: Vec<_> = files
        .iter()
        .map(|(name, bytes)| (name, digest(bytes)))
        .collect();
    digest(
        format!(
            "{}\n{}",
            super::crate_inputs::PROFILE_ID,
            serde_json::to_string(&hashes).unwrap()
        )
        .as_bytes(),
    )
}
fn decode(
    bytes: &[u8],
    c: &Config,
    files: &super::crate_inputs::SourceFiles,
) -> Result<RustExport, String> {
    let export = if c.crate_config.is_some() {
        super::charon::decode_crate(
            bytes,
            &c.source,
            &files[&c.source],
            c.crate_config.as_ref(),
            Some(files),
        )?
    } else {
        super::charon::decode(bytes, &c.source, &files[&c.source])?
    };
    super::lowering::lower(&export)?;
    Ok(export)
}
fn write_atomic(path: &Path, bytes: &[u8]) -> Result<(), String> {
    match fs::symlink_metadata(path) {
        Ok(m) if !m.file_type().is_file() => {
            return Err("Rust output must be a regular file".into());
        }
        Err(e) if e.kind() != std::io::ErrorKind::NotFound => return Err(e.to_string()),
        _ => {}
    }
    crate::cli::write_file_atomically(path, bytes)
}
pub fn refresh_import(path: &Path) -> Result<(), String> {
    let (c, bytes, root) = config(path)?;
    let source = if c.crate_config.is_some() {
        super::crate_inputs::file(&root, &c.source)?
    } else {
        local_file(&root, &c.source)?
    };
    let source_files = sources(&c, &root)?;
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
    let driver = exporter.with_file_name("charon-driver");
    if driver == artifact_path || driver == lock_output {
        return Err("Charon driver must differ from artifact/lock outputs".into());
    }
    let driver_bytes = read(&driver, 128 << 20)?;
    let driver_hash = digest(&driver_bytes);
    let output_bytes = if c.crate_config.is_some() {
        super::charon::extract_crate(
            &exporter,
            &source,
            &root,
            c.crate_config.as_ref(),
            Some(&source_files),
        )?
    } else {
        super::charon::extract(&exporter, &source, &root)?
    };
    if driver_bytes != read(&driver, 128 << 20)? {
        return Err("Charon driver changed during extraction".into());
    }
    decode(&output_bytes, &c, &source_files)?;
    if bytes != read(path, 1 << 20)?
        || source_files != sources(&c, &root)?
        || exporter_bytes != read(&exporter, 128 << 20)?
    {
        return Err("Rust inputs changed during compiler extraction".into());
    }
    let config_hash = digest(&bytes);
    let source_hash = source_digest(&c, &source_files);
    let exporter_hash = digest(&exporter_bytes);
    let artifact_hash = digest(&output_bytes);
    let lock = Lock {
        schema: SCHEMA,
        identity: import_identity(
            &config_hash,
            &source_hash,
            &exporter_hash,
            &artifact_hash,
            &driver_hash,
        ),
        charon_driver: Some(driver_hash),
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
    let source_files = sources(&c, &root)?;
    if lock.schema != SCHEMA
        || lock.config != digest(&bytes)
        || lock.source != source_digest(&c, &source_files)
        || lock.artifact != digest(&artifact)
        || lock.charon_driver.is_none()
        || lock.identity
            != import_identity(
                &lock.config,
                &lock.source,
                &lock.exporter,
                &lock.artifact,
                lock.charon_driver.as_deref().unwrap_or_default(),
            )
    {
        return Err("Rust import lock differs from its inputs; refresh it".into());
    }
    let export = decode(&artifact, &c, &source_files)?;
    Ok(PreparedRustImport {
        inner: Arc::new(Inner {
            export,
            identity: lock.identity,
            execution: Default::default(),
        }),
    })
}
