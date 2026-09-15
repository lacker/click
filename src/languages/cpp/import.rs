//! Locked semantic imports produced by the pinned C++ frontend.
//!
//! `refresh_import` is the only operation in this module that executes the
//! Clang-based exporter. `load_import` validates the source, lock, and stored
//! semantic artifact without consulting or executing the exporter.

use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::schema::{CppExport, CppProfile, EXPORT_SCHEMA, LANGUAGE, STANDARD, TARGET};
use crate::languages::compiler_process::{CompilerLimits, run_compiler};

const CONFIG_SCHEMA: u32 = 2;
const MAX_CONFIG_BYTES: usize = 1 << 20;
const MAX_COMPILATION_DATABASE_BYTES: usize = 16 << 20;
const MAX_SOURCE_BYTES: usize = 1 << 20;
const MAX_EXPORTER_BYTES: usize = 64 << 20;
const MAX_ARTIFACT_BYTES: usize = 8 << 20;
const MAX_DIAGNOSTIC_BYTES: usize = 64 << 10;

#[derive(Clone, Debug)]
pub struct PreparedCppImport {
    inner: Arc<PreparedInner>,
}

#[derive(Debug)]
struct PreparedInner {
    logical_source: String,
    identity: String,
    export: CppExport,
}

impl PreparedCppImport {
    pub fn logical_source(&self) -> &str {
        &self.inner.logical_source
    }

    pub fn identity(&self) -> &str {
        &self.inner.identity
    }

    pub fn export(&self) -> &CppExport {
        &self.inner.export
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    schema: u32,
    language: String,
    standard: String,
    target: String,
    exceptions: bool,
    rtti: bool,
    exporter: String,
    compilation_database: String,
    working_directory: String,
    source: String,
    logical_source: String,
    function: String,
    artifact: String,
    #[serde(skip)]
    directory: PathBuf,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct Lock {
    schema: u32,
    config_sha256: String,
    exporter_sha256: String,
    compilation_database_sha256: String,
    source_sha256: String,
    artifact_sha256: String,
    artifact_bytes: usize,
    profile: CppProfile,
    identity: String,
}

pub fn refresh_import(config_path: &Path) -> Result<(), String> {
    refresh_import_inner(config_path).map_err(bounded_error)
}

fn refresh_import_inner(config_path: &Path) -> Result<(), String> {
    let (config, config_bytes) = read_config(config_path)?;
    let exporter = resolve_input(&config.directory, &config.exporter, "C++ exporter")?;
    let compilation_database = resolve_input(
        &config.directory,
        &config.compilation_database,
        "C++ compilation database",
    )?;
    let working_directory = resolve_input(
        &config.directory,
        &config.working_directory,
        "C++ working directory",
    )?;
    if !working_directory.is_dir() {
        return Err(format!(
            "C++ working directory `{}` is not a directory",
            working_directory.display()
        ));
    }
    let source = resolve_source(&config, &working_directory)?;
    reject_output_collisions(
        config_path,
        &config,
        &source,
        &exporter,
        &compilation_database,
    )?;

    let exporter_bytes = read_stable(&exporter, MAX_EXPORTER_BYTES, "C++ exporter")?;
    let compilation_database_before = read_stable(
        &compilation_database,
        MAX_COMPILATION_DATABASE_BYTES,
        "C++ compilation database",
    )?;
    let source_before = read_stable(&source, MAX_SOURCE_BYTES, "C++ source")?;
    let arguments = vec![
        "--logical-source".into(),
        config.logical_source.clone(),
        "--function".into(),
        config.function.clone(),
        "--source".into(),
        source.to_string_lossy().into_owned(),
        "--compilation-database".into(),
        compilation_database.to_string_lossy().into_owned(),
    ];
    let output = run_compiler(
        &exporter,
        &arguments,
        &working_directory,
        &BTreeMap::new(),
        CompilerLimits {
            timeout: Duration::from_secs(10),
            max_stdout_bytes: MAX_ARTIFACT_BYTES,
            max_stderr_bytes: MAX_DIAGNOSTIC_BYTES,
        },
    )
    .map_err(|error| format!("export C++ source `{}`: {error}", config.logical_source))?;
    if !output.stderr.is_empty() {
        return Err(format!(
            "C++ exporter emitted diagnostics: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    if read_stable(&source, MAX_SOURCE_BYTES, "C++ source")? != source_before {
        return Err("C++ source changed during semantic export".into());
    }
    if read_stable(&exporter, MAX_EXPORTER_BYTES, "C++ exporter")? != exporter_bytes {
        return Err("C++ exporter changed during semantic export".into());
    }
    if read_stable(
        &compilation_database,
        MAX_COMPILATION_DATABASE_BYTES,
        "C++ compilation database",
    )? != compilation_database_before
    {
        return Err("C++ compilation database changed during semantic export".into());
    }

    let export = decode_artifact(&output.stdout, &config)?;
    let config_sha256 = hex_digest(&config_bytes);
    let exporter_sha256 = hex_digest(&exporter_bytes);
    let compilation_database_sha256 = hex_digest(&compilation_database_before);
    let source_sha256 = hex_digest(&source_before);
    let artifact_sha256 = hex_digest(&output.stdout);
    let identity = semantic_identity(
        &config_sha256,
        &compilation_database_sha256,
        &source_sha256,
        &exporter_sha256,
        &artifact_sha256,
        &export.profile,
    );
    let lock = Lock {
        schema: CONFIG_SCHEMA,
        config_sha256,
        exporter_sha256,
        compilation_database_sha256,
        source_sha256,
        artifact_sha256,
        artifact_bytes: output.stdout.len(),
        profile: export.profile,
        identity,
    };
    let mut lock_bytes =
        serde_json::to_vec_pretty(&lock).map_err(|error| format!("encode C++ lock: {error}"))?;
    lock_bytes.push(b'\n');
    if lock_bytes.len() > MAX_CONFIG_BYTES {
        return Err("C++ import lock exceeds its size limit".into());
    }

    atomic_write(&artifact_path(&config)?, &output.stdout)?;
    atomic_write(&lock_path(config_path)?, &lock_bytes)
}

pub fn load_import(config_path: &Path) -> Result<PreparedCppImport, String> {
    load_import_inner(config_path).map_err(bounded_error)
}

fn load_import_inner(config_path: &Path) -> Result<PreparedCppImport, String> {
    let (config, config_bytes) = read_config(config_path)?;
    let lock_bytes = read_stable(
        &lock_path(config_path)?,
        MAX_CONFIG_BYTES,
        "C++ import lock",
    )?;
    let lock: Lock = serde_json::from_slice(&lock_bytes)
        .map_err(|error| format!("parse C++ import lock: {error}"))?;
    if lock.schema != CONFIG_SCHEMA {
        return Err(format!(
            "unsupported C++ import lock schema {}; expected {CONFIG_SCHEMA}",
            lock.schema
        ));
    }
    if lock.config_sha256 != hex_digest(&config_bytes) {
        return Err("C++ import lock does not match the import config; refresh it".into());
    }

    let compilation_database = resolve_input(
        &config.directory,
        &config.compilation_database,
        "C++ compilation database",
    )?;
    let compilation_database_bytes = read_stable(
        &compilation_database,
        MAX_COMPILATION_DATABASE_BYTES,
        "C++ compilation database",
    )?;
    if lock.compilation_database_sha256 != hex_digest(&compilation_database_bytes) {
        return Err("C++ compilation database differs from the import lock; refresh it".into());
    }

    let working_directory = resolve_input(
        &config.directory,
        &config.working_directory,
        "C++ working directory",
    )?;
    let source = resolve_source(&config, &working_directory)?;
    let source_bytes = read_stable(&source, MAX_SOURCE_BYTES, "C++ source")?;
    if lock.source_sha256 != hex_digest(&source_bytes) {
        return Err("C++ source differs from the import lock; refresh it".into());
    }
    let artifact = read_stable(
        &artifact_path(&config)?,
        MAX_ARTIFACT_BYTES,
        "C++ semantic artifact",
    )?;
    if lock.artifact_bytes != artifact.len() || lock.artifact_sha256 != hex_digest(&artifact) {
        return Err("C++ semantic artifact differs from the import lock; refresh it".into());
    }
    let export = decode_artifact(&artifact, &config)?;
    if lock.profile != export.profile {
        return Err("C++ semantic artifact profile differs from the import lock".into());
    }
    let identity = semantic_identity(
        &lock.config_sha256,
        &lock.compilation_database_sha256,
        &lock.source_sha256,
        &lock.exporter_sha256,
        &lock.artifact_sha256,
        &lock.profile,
    );
    if lock.identity != identity {
        return Err("C++ import identity does not match its locked inputs".into());
    }

    Ok(PreparedCppImport {
        inner: Arc::new(PreparedInner {
            logical_source: config.logical_source,
            identity,
            export,
        }),
    })
}

fn decode_artifact(bytes: &[u8], config: &Config) -> Result<CppExport, String> {
    let export: CppExport = serde_json::from_slice(bytes)
        .map_err(|error| format!("parse C++ semantic artifact: {error}"))?;
    export.validate(&config.logical_source, &config.function)?;
    Ok(export)
}

fn semantic_identity(
    config_sha256: &str,
    compilation_database_sha256: &str,
    source_sha256: &str,
    exporter_sha256: &str,
    artifact_sha256: &str,
    profile: &CppProfile,
) -> String {
    let encoded = serde_json::to_vec(&(
        CONFIG_SCHEMA,
        EXPORT_SCHEMA,
        "click-cpp-semantic-import-v2",
        config_sha256,
        compilation_database_sha256,
        source_sha256,
        exporter_sha256,
        artifact_sha256,
        profile,
    ))
    .expect("C++ semantic identity serializes");
    hex_digest(&encoded)
}

fn read_config(path: &Path) -> Result<(Config, Vec<u8>), String> {
    let absolute = absolute_path(path)?;
    let bytes = read_stable(&absolute, MAX_CONFIG_BYTES, "C++ import config")?;
    let mut config: Config = serde_json::from_slice(&bytes)
        .map_err(|error| format!("parse C++ import config: {error}"))?;
    config.directory = absolute
        .parent()
        .ok_or("C++ import config has no parent directory")?
        .to_path_buf();
    validate_config(&config)?;
    Ok((config, bytes))
}

fn validate_config(config: &Config) -> Result<(), String> {
    if config.schema != CONFIG_SCHEMA
        || config.language != LANGUAGE
        || config.standard != STANDARD
        || config.target != TARGET
        || config.exceptions
        || config.rtti
    {
        return Err(format!(
            "C++ import config must use schema {CONFIG_SCHEMA}, Clang {STANDARD} for {TARGET}, with exceptions and RTTI disabled"
        ));
    }
    for (label, value) in [
        ("exporter", config.exporter.as_str()),
        ("compilation database", config.compilation_database.as_str()),
        ("working directory", config.working_directory.as_str()),
        ("source", config.source.as_str()),
        ("logical source", config.logical_source.as_str()),
        ("function", config.function.as_str()),
        ("artifact", config.artifact.as_str()),
    ] {
        if value.is_empty() || value.as_bytes().contains(&0) {
            return Err(format!("C++ import config has invalid {label}"));
        }
    }
    validate_relative_path(&config.source, "source")?;
    validate_relative_path(&config.compilation_database, "compilation database")?;
    validate_relative_path(&config.logical_source, "logical source")?;
    validate_relative_path(&config.artifact, "artifact")?;
    if Path::new(&config.source)
        .extension()
        .and_then(|value| value.to_str())
        != Some("cpp")
        || Path::new(&config.logical_source)
            .extension()
            .and_then(|value| value.to_str())
            != Some("cpp")
    {
        return Err("the first C++ import slice requires a `.cpp` source".into());
    }
    if !is_identifier(&config.function) {
        return Err("the first C++ import slice requires an unqualified function name".into());
    }
    if config.source == config.artifact || config.logical_source == config.artifact {
        return Err("C++ source and semantic artifact paths must differ".into());
    }
    Ok(())
}

fn is_identifier(value: &str) -> bool {
    let mut chars = value.chars();
    chars
        .next()
        .is_some_and(|first| first == '_' || first.is_ascii_alphabetic())
        && chars.all(|character| character == '_' || character.is_ascii_alphanumeric())
}

fn validate_relative_path(path: &str, label: &str) -> Result<(), String> {
    let path = Path::new(path);
    if path.is_absolute()
        || path.components().any(|component| {
            matches!(
                component,
                Component::ParentDir | Component::RootDir | Component::Prefix(_)
            )
        })
    {
        return Err(format!(
            "C++ {label} path must stay inside its configured root"
        ));
    }
    Ok(())
}

fn absolute_path(path: &Path) -> Result<PathBuf, String> {
    let joined = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|error| format!("read current directory: {error}"))?
            .join(path)
    };
    joined
        .canonicalize()
        .map_err(|error| format!("resolve `{}`: {error}", joined.display()))
}

fn resolve_input(base: &Path, path: &str, label: &str) -> Result<PathBuf, String> {
    let path = Path::new(path);
    let joined = if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    };
    joined
        .canonicalize()
        .map_err(|error| format!("resolve {label} `{}`: {error}", joined.display()))
}

fn resolve_source(config: &Config, working_directory: &Path) -> Result<PathBuf, String> {
    resolve_input(working_directory, &config.source, "C++ source")
}

fn artifact_path(config: &Config) -> Result<PathBuf, String> {
    validate_relative_path(&config.artifact, "artifact")?;
    Ok(config.directory.join(&config.artifact))
}

fn lock_path(config_path: &Path) -> Result<PathBuf, String> {
    let absolute = if config_path.is_absolute() {
        config_path.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|error| format!("read current directory: {error}"))?
            .join(config_path)
    };
    let name = absolute
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or("C++ import config path has no UTF-8 filename")?;
    Ok(absolute.with_file_name(format!("{name}.lock")))
}

fn reject_output_collisions(
    config_path: &Path,
    config: &Config,
    source: &Path,
    exporter: &Path,
    compilation_database: &Path,
) -> Result<(), String> {
    let config_path = absolute_path(config_path)?;
    let artifact = artifact_path(config)?;
    let lock = lock_path(&config_path)?;
    for (output_label, output) in [("artifact", &artifact), ("lock", &lock)] {
        for (input_label, input) in [
            ("config", config_path.as_path()),
            ("source", source),
            ("exporter", exporter),
            ("compilation database", compilation_database),
        ] {
            if output == input {
                return Err(format!(
                    "C++ {output_label} output collides with the {input_label} input"
                ));
            }
        }
    }
    if artifact == lock {
        return Err("C++ artifact and lock outputs collide".into());
    }
    Ok(())
}

fn read_stable(path: &Path, max: usize, label: &str) -> Result<Vec<u8>, String> {
    let before = fs::symlink_metadata(path)
        .map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
    if !before.file_type().is_file() {
        return Err(format!(
            "{label} `{}` is not a regular file",
            path.display()
        ));
    }
    if before.len() > max as u64 {
        return Err(format!("{label} exceeds its {max}-byte limit"));
    }
    let bytes =
        fs::read(path).map_err(|error| format!("read {label} `{}`: {error}", path.display()))?;
    if bytes.len() > max {
        return Err(format!("{label} exceeds its {max}-byte limit"));
    }
    let after = fs::symlink_metadata(path)
        .map_err(|error| format!("re-read {label} `{}`: {error}", path.display()))?;
    if before.len() != after.len() || before.modified().ok() != after.modified().ok() {
        return Err(format!(
            "{label} `{}` changed while being read",
            path.display()
        ));
    }
    Ok(bytes)
}

fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let parent = path
        .parent()
        .ok_or_else(|| format!("output `{}` has no parent", path.display()))?;
    fs::create_dir_all(parent)
        .map_err(|error| format!("create output directory `{}`: {error}", parent.display()))?;
    let temporary = path.with_extension(format!("tmp-{}", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .map_err(|error| format!("create temporary output `{}`: {error}", temporary.display()))?;
    let result = (|| {
        file.write_all(bytes)
            .map_err(|error| format!("write temporary output: {error}"))?;
        file.sync_all()
            .map_err(|error| format!("sync temporary output: {error}"))?;
        fs::rename(&temporary, path)
            .map_err(|error| format!("replace output `{}`: {error}", path.display()))
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

fn hex_digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn bounded_error(error: String) -> String {
    const MAX_CHARS: usize = 8_000;
    if error.chars().count() <= MAX_CHARS {
        error
    } else {
        format!(
            "{}... [diagnostic truncated]",
            error.chars().take(MAX_CHARS).collect::<String>()
        )
    }
}
