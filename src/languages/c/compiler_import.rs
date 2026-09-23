//! Strict, reproducible compiler-backed C imports.
//!
//! This module owns the declarative import/lock format.  Process ownership is
//! deliberately delegated to `compiler_process`; this layer validates the
//! invocation and snapshots dependencies during explicit refresh. Ordinary
//! loading checks the recorded artifact without running the compiler.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::provenance::CSourceMap;
use super::target::CTarget;
use crate::languages::compiler_process::{CompilerLimits, run_compiler};

const SCHEMA: u32 = 1;
const LOCK_SCHEMA: u32 = 2;
const MAX_CONFIG_BYTES: usize = 1 << 20;
const MAX_SOURCES: usize = 4096;
const MAX_ARGUMENTS: usize = 4096;
const MAX_ARGUMENT_BYTES: usize = 1 << 20;
const MAX_SOURCE_BYTES: u64 = 64 << 20;
const MAX_ARTIFACT_BYTES: usize = 64 << 20;
const MAX_DEPENDENCIES: usize = 100_000;
const MAX_ROOT_ENTRIES: usize = 200_000;
const MAX_ROOT_BYTES: u64 = 512 << 20;
const MAX_PROJECT_ARTIFACT_BYTES: usize = 128 << 20;

#[derive(Clone, Debug)]
pub struct PreparedCImport {
    inner: Arc<PreparedInner>,
}

#[derive(Debug)]
struct PreparedInner {
    target: CTarget,
    logical_source: String,
    source: String,
    source_map: CSourceMap,
    identity: String,
}

impl PreparedCImport {
    pub fn target(&self) -> CTarget {
        self.inner.target
    }

    pub fn logical_source(&self) -> &str {
        &self.inner.logical_source
    }
    pub fn source(&self) -> &str {
        &self.inner.source
    }
    pub fn source_map(&self) -> &CSourceMap {
        &self.inner.source_map
    }
    pub fn identity(&self) -> &str {
        &self.inner.identity
    }

    #[cfg(test)]
    pub(crate) fn for_test(logical_source: &str, source: &str) -> Self {
        let (source, source_map) = CSourceMap::decode(source).expect("test source map");
        Self {
            inner: Arc::new(PreparedInner {
                target: CTarget::SUPPORTED,
                logical_source: logical_source.to_string(),
                source,
                source_map,
                identity: format!("test-{logical_source}"),
            }),
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    schema: u32,
    target: String,
    compiler: PathBuf,
    working_directory: String,
    environment: Environment,
    sources: Vec<SourceConfig>,
    #[serde(skip)]
    config_directory: PathBuf,
    #[serde(skip)]
    lock_path: PathBuf,
    #[serde(skip)]
    config_path: PathBuf,
    #[serde(skip)]
    config_bytes_sha256: String,
}

impl Config {
    // Configs enter the compiler path only after validate_config.
    fn c_target(&self) -> CTarget {
        CTarget::from_name(&self.target).expect("validated compiler target")
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Environment {
    allow: BTreeMap<String, String>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct SourceConfig {
    logical_source: String,
    path: String,
    args: Vec<String>,
    artifact: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Lock {
    schema: u32,
    config_sha256: String,
    target: String,
    compiler_path: String,
    working_directory: String,
    config_directory: String,
    invocation_sha256: String,
    toolchain: ToolchainIdentity,
    sources: Vec<LockedSource>,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct ToolchainIdentity {
    driver_sha256: String,
    cc1_path: String,
    cc1_sha256: String,
    resource_files: BTreeMap<String, String>,
    specs_path: Option<String>,
    specs_sha256: Option<String>,
    abi_probe_sha256: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct LockedSource {
    logical_source: String,
    path: String,
    args: Vec<String>,
    artifact: String,
    source_sha256: String,
    artifact_sha256: String,
    artifact_bytes: usize,
    dependencies: BTreeMap<String, String>,
    local_dependencies: BTreeMap<String, String>,
    identity: String,
}

#[derive(Clone, Copy)]
enum ConfigUse {
    Prepare,
    Load,
}

#[derive(Clone, Debug)]
struct Preprocessed {
    artifact: Vec<u8>,
    dependencies: BTreeMap<String, String>,
    local_dependencies: BTreeMap<String, String>,
    source_sha256: String,
    identity: String,
}

#[derive(Clone, Debug)]
struct Context<'a> {
    config: &'a Config,
    invocation_sha256: String,
    toolchain: ToolchainIdentity,
    toolchain_generation: BTreeMap<String, FileState>,
    roots: Vec<PathBuf>,
    exclusions: BTreeSet<PathBuf>,
    before: RootSnapshot,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FileState {
    kind: u8,
    len: u64,
    modified: u128,
    changed: u128,
    inode: u64,
    content_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RootSnapshot {
    entries: BTreeMap<String, FileState>,
    bytes: u64,
}

pub fn load_imports(config_path: &Path) -> Result<Vec<PreparedCImport>, String> {
    load_imports_inner(config_path).map_err(bounded_error)
}

fn load_imports_inner(config_path: &Path) -> Result<Vec<PreparedCImport>, String> {
    let (config, config_bytes) = read_config(config_path, ConfigUse::Load)?;
    let lock_path = lock_path(config_path);
    let lock_bytes = read_bounded(&lock_path, MAX_CONFIG_BYTES, "import lock")?;
    reject_duplicate_json_keys(&lock_bytes)?;
    let lock: Lock =
        serde_json::from_slice(&lock_bytes).map_err(|e| format!("parse import lock: {e}"))?;
    validate_lock_shape(&lock, &config)?;
    if lock.config_sha256 != hex_digest(&config_bytes) {
        return Err("import lock does not match the import config".into());
    }
    if lock.invocation_sha256
        != invocation_digest_parts(
            &config.target,
            &lock.compiler_path,
            &lock.working_directory,
            &config.environment.allow,
            &lock.toolchain,
        )
    {
        return Err("compiler invocation identity differs from the import lock".into());
    }
    let locked_by_name = lock
        .sources
        .iter()
        .map(|source| (source.logical_source.as_str(), source))
        .collect::<BTreeMap<_, _>>();
    let mut prepared = Vec::with_capacity(config.sources.len());
    let mut artifact_bytes = 0usize;
    for source in &config.sources {
        let locked = locked_by_name
            .get(source.logical_source.as_str())
            .ok_or_else(|| format!("lock has no source `{}`", source.logical_source))?;
        validate_locked_source(
            source,
            locked,
            &config,
            &lock.invocation_sha256,
            &lock.config_directory,
        )?;
        let artifact_path = resolve_artifact(&config, &source.artifact)?;
        let existing = read_stable(&artifact_path, MAX_ARTIFACT_BYTES, "locked artifact")?;
        charge_artifact_bytes(&mut artifact_bytes, existing.len())?;
        if existing.len() != locked.artifact_bytes
            || hex_digest(&existing) != locked.artifact_sha256
        {
            return Err(format!(
                "locked artifact `{}` differs from its lock",
                artifact_path.display()
            ));
        }
        let text = std::str::from_utf8(&existing)
            .map_err(|e| format!("compiler output is not UTF-8: {e}"))?;
        let (clean, map) = CSourceMap::decode(text)?;
        prepared.push(PreparedCImport {
            inner: Arc::new(PreparedInner {
                target: config.c_target(),
                logical_source: source.logical_source.clone(),
                source: clean,
                source_map: map,
                identity: locked.identity.clone(),
            }),
        });
    }
    Ok(prepared)
}

pub fn create_lock(config_path: &Path) -> Result<(), String> {
    create_lock_inner(config_path).map_err(bounded_error)
}

fn create_lock_inner(config_path: &Path) -> Result<(), String> {
    let (config, config_bytes) = read_config(config_path, ConfigUse::Prepare)?;
    let context = make_context(&config)?;
    let mut results = Vec::with_capacity(config.sources.len());
    let mut artifact_bytes = 0usize;
    for source in &config.sources {
        let result = preprocess(&context, source)?;
        charge_artifact_bytes(&mut artifact_bytes, result.artifact.len())?;
        results.push((source, result));
    }
    verify_roots(&context)?;
    let mut locked = Vec::with_capacity(results.len());
    for (source, result) in &results {
        locked.push(LockedSource {
            logical_source: source.logical_source.clone(),
            path: source.path.clone(),
            args: source.args.clone(),
            artifact: source.artifact.clone(),
            source_sha256: result.source_sha256.clone(),
            artifact_sha256: hex_digest(&result.artifact),
            artifact_bytes: result.artifact.len(),
            dependencies: result.dependencies.clone(),
            local_dependencies: result.local_dependencies.clone(),
            identity: result.identity.clone(),
        });
    }
    let lock = Lock {
        schema: LOCK_SCHEMA,
        config_sha256: hex_digest(&config_bytes),
        target: config.target.clone(),
        compiler_path: config.compiler.to_string_lossy().into_owned(),
        working_directory: config.working_directory.clone(),
        config_directory: fs::canonicalize(&config.config_directory)
            .map_err(|error| format!("resolve project root: {error}"))?
            .to_string_lossy()
            .into_owned(),
        invocation_sha256: context.invocation_sha256.clone(),
        toolchain: context.toolchain.clone(),
        sources: locked,
    };
    let mut encoded =
        serde_json::to_vec_pretty(&lock).map_err(|e| format!("encode import lock: {e}"))?;
    encoded.push(b'\n');
    if encoded.len() > MAX_CONFIG_BYTES {
        return Err("import lock exceeds the supported size bound".into());
    }
    for (source, result) in &results {
        atomic_write(
            &resolve_artifact(&config, &source.artifact)?,
            &result.artifact,
        )?;
    }
    atomic_write(&lock_path(config_path), &encoded)
}

fn read_config(config_path: &Path, use_for: ConfigUse) -> Result<(Config, Vec<u8>), String> {
    let absolute = absolute_path(config_path, Path::new("."))?;
    reject_symlink_components(&absolute)?;
    let bytes = read_stable(&absolute, MAX_CONFIG_BYTES, "import config")?;
    reject_duplicate_json_keys(&bytes)?;
    let mut config: Config =
        serde_json::from_slice(&bytes).map_err(|e| format!("parse import config: {e}"))?;
    config.config_directory = absolute
        .parent()
        .ok_or("import config has no parent")?
        .to_path_buf();
    config.lock_path = lock_path(&absolute);
    config.config_path = absolute.clone();
    config.config_bytes_sha256 = hex_digest(&bytes);
    normalize_config(&mut config, use_for)?;
    validate_config(&config, use_for)?;
    Ok((config, bytes))
}

fn make_context(config: &Config) -> Result<Context<'_>, String> {
    if file_digest(&config.config_path)? != config.config_bytes_sha256 {
        return Err("import config changed while it was being loaded".into());
    }
    let roots = canonicalize_roots(&explicit_roots(config)?)?;
    let exclusions = output_exclusions(config)?;
    let (toolchain, toolchain_generation) = discover_toolchain(config)?;
    let invocation_sha256 = invocation_digest(config, &toolchain);
    let before = snapshot_roots(&roots, &exclusions)?;
    if file_digest(&config.config_path)? != config.config_bytes_sha256 {
        return Err("import config changed while the input snapshot was taken".into());
    }
    Ok(Context {
        config,
        invocation_sha256,
        toolchain,
        toolchain_generation,
        roots,
        exclusions,
        before,
    })
}

fn preprocess(context: &Context<'_>, source: &SourceConfig) -> Result<Preprocessed, String> {
    let invocation_source = Path::new(&source.path);
    let source_path = resolve_source(context.config, &source.path)?;
    let canonical_source = path_identity(&source_path)?;
    if !root_contains(&context.roots, &canonical_source) {
        return Err(format!(
            "source {} is outside the declared input roots",
            source_path.display()
        ));
    }
    let metadata = fs::metadata(&source_path)
        .map_err(|e| format!("read source {}: {e}", source_path.display()))?;
    if !metadata.is_file() {
        return Err(format!(
            "source {} is not a regular file",
            source_path.display()
        ));
    }
    if metadata.len() > MAX_SOURCE_BYTES {
        return Err(format!("source exceeds {} bytes", MAX_SOURCE_BYTES));
    }
    let dep_path = unique_temp_path("click-import-deps", ".d")?;
    let _cleanup = RemoveFile(dep_path.clone());
    let mut args = fixed_args(context.config.c_target());
    append_user_args(&mut args, &source.args, context.config.c_target())?;
    args.extend([
        "-x".into(),
        "c".into(),
        "-E".into(),
        "-MD".into(),
        "-MF".into(),
        dep_path.to_string_lossy().into_owned(),
        invocation_source.to_string_lossy().into_owned(),
    ]);
    let output = match run_compiler(
        &context.config.compiler,
        &args,
        Path::new(&context.config.working_directory),
        &context.config.environment.allow,
        limits(),
    ) {
        Ok(output) => output,
        Err(error) => {
            let _ = fs::remove_file(&dep_path);
            return Err(format!("preprocess {}: {error}", source.logical_source));
        }
    };
    let dep = read_bounded(&dep_path, MAX_CONFIG_BYTES, "compiler dependency output");
    let _ = fs::remove_file(&dep_path);
    let dep = dep?;
    if output.stdout.len() > MAX_ARTIFACT_BYTES {
        return Err(format!(
            "preprocessed artifact exceeds {} bytes",
            MAX_ARTIFACT_BYTES
        ));
    }
    if !output.stderr.is_empty() {
        return Err(format!(
            "compiler diagnostics: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let dependencies = parse_dependencies(
        &dep,
        &source_path,
        &context.config.working_directory,
        &context.roots,
        &context.exclusions,
    )?;
    let source_sha256 = file_digest(&source_path)?;
    let local_dependencies = local_dependencies(context.config, &dependencies)?;
    let mut result = Preprocessed {
        artifact: output.stdout,
        dependencies,
        local_dependencies,
        source_sha256,
        identity: String::new(),
    };
    result.identity = source_identity(context.config, context, source, &result);
    Ok(result)
}

fn local_dependencies(
    config: &Config,
    dependencies: &BTreeMap<String, String>,
) -> Result<BTreeMap<String, String>, String> {
    let root = fs::canonicalize(&config.config_directory)
        .map_err(|error| format!("resolve project root: {error}"))?;
    Ok(dependencies
        .iter()
        .filter_map(|(path, digest)| {
            Path::new(path)
                .strip_prefix(&root)
                .ok()
                .map(|relative| (relative.to_string_lossy().into_owned(), digest.clone()))
        })
        .collect())
}

fn validate_locked_source(
    source: &SourceConfig,
    locked: &LockedSource,
    config: &Config,
    invocation_sha256: &str,
    preparation_root: &str,
) -> Result<(), String> {
    if locked.logical_source != source.logical_source
        || locked.path != source.path
        || locked.args != source.args
        || locked.artifact != source.artifact
    {
        return Err(format!(
            "lock source entry for {} does not match config",
            source.logical_source
        ));
    }
    let source_path = resolve_source(config, &source.path)?;
    if file_digest(&source_path)? != locked.source_sha256 {
        return Err(format!(
            "source `{}` differs from its import lock",
            source_path.display()
        ));
    }
    let projected = locked
        .dependencies
        .iter()
        .filter_map(|(path, digest)| {
            Path::new(path)
                .strip_prefix(preparation_root)
                .ok()
                .map(|relative| (relative.to_string_lossy().into_owned(), digest.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    if projected != locked.local_dependencies {
        return Err("local dependency inventory differs from the import lock".into());
    }
    for (relative, expected) in &locked.local_dependencies {
        let relative = Path::new(relative);
        if relative
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_)))
        {
            return Err("import lock has an invalid local dependency path".into());
        }
        let path = config.config_directory.join(relative);
        reject_symlink_components(&path)?;
        if file_digest(&path)? != *expected {
            return Err(format!(
                "local dependency `{}` differs from its import lock",
                path.display()
            ));
        }
    }
    let identity = source_identity_parts(
        &config.target,
        invocation_sha256,
        source,
        &locked.source_sha256,
        &locked.dependencies,
        &locked.local_dependencies,
        &locked.artifact_sha256,
    );
    if identity != locked.identity {
        return Err(format!(
            "source identity for {} differs from its import lock",
            source.logical_source
        ));
    }
    Ok(())
}

fn source_identity(
    config: &Config,
    context: &Context<'_>,
    source: &SourceConfig,
    result: &Preprocessed,
) -> String {
    source_identity_parts(
        &config.target,
        &context.invocation_sha256,
        source,
        &result.source_sha256,
        &result.dependencies,
        &result.local_dependencies,
        &hex_digest(&result.artifact),
    )
}

fn source_identity_parts(
    target: &str,
    invocation_sha256: &str,
    source: &SourceConfig,
    source_sha256: &str,
    dependencies: &BTreeMap<String, String>,
    local_dependencies: &BTreeMap<String, String>,
    artifact_sha256: &str,
) -> String {
    let data = serde_json::to_vec(&(
        LOCK_SCHEMA,
        "c-source-projection-v2",
        target,
        invocation_sha256,
        source.logical_source.as_str(),
        source.path.as_str(),
        &source.args,
        source.artifact.as_str(),
        source_sha256,
        dependencies,
        local_dependencies,
        artifact_sha256,
    ))
    .expect("identity serializes");
    hex_digest(&data)
}

fn fixed_args(target: CTarget) -> Vec<String> {
    let standard = match target {
        CTarget::X86_64LinuxKernel => "-std=gnu11",
        CTarget::X86_64LinuxUserspace => "-std=c11",
    };
    let mut args = vec![
        standard.into(),
        "-m64".into(),
        "-funsigned-char".into(),
        "-nostdinc".into(),
    ];
    if target == CTarget::X86_64LinuxUserspace {
        args.extend(["-pthread".into(), "-D_POSIX_C_SOURCE=200809L".into()]);
    }
    args
}
fn append_user_args(out: &mut Vec<String>, args: &[String], target: CTarget) -> Result<(), String> {
    validate_args(args, target)?;
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        out.push(arg.clone());
        if matches!(arg.as_str(), "-D" | "-U" | "-I" | "-isystem" | "-include") {
            i += 1;
            out.push(args[i].clone());
        }
        i += 1;
    }
    Ok(())
}

fn parse_dependencies(
    bytes: &[u8],
    source: &Path,
    cwd: &str,
    roots: &[PathBuf],
    exclusions: &BTreeSet<PathBuf>,
) -> Result<BTreeMap<String, String>, String> {
    let text =
        std::str::from_utf8(bytes).map_err(|e| format!("dependency output is not UTF-8: {e}"))?;
    let mut tokens = dep_tokens(text)?;
    if tokens.is_empty() {
        return Err("malformed compiler dependency output".into());
    }
    tokens.remove(0);
    let canonical_source = fs::canonicalize(source)
        .map_err(|e| format!("canonicalize source {}: {e}", source.display()))?;
    let mut result = BTreeMap::new();
    for token in tokens {
        let path = absolute_path(Path::new(&token), Path::new(cwd))?;
        let canonical = fs::canonicalize(&path)
            .map_err(|e| format!("canonicalize compiler dependency {}: {e}", path.display()))?;
        if canonical == canonical_source {
            continue;
        }
        if !root_contains(roots, &canonical) {
            return Err(format!(
                "dependency {} is outside the declared input roots",
                path.display()
            ));
        }
        if exclusions.contains(&canonical) {
            return Err(format!(
                "dependency {} overlaps an owned output",
                path.display()
            ));
        }
        if result.len() >= MAX_DEPENDENCIES {
            return Err("dependency inventory exceeds bound".into());
        }
        let key = canonical.to_string_lossy().into_owned();
        if let std::collections::btree_map::Entry::Vacant(entry) = result.entry(key) {
            entry.insert(file_digest(&path)?);
        }
    }
    Ok(result)
}

fn dep_tokens(text: &str) -> Result<Vec<String>, String> {
    let mut out = Vec::new();
    let mut current = String::new();
    let mut escaped = false;
    let mut saw_colon = false;
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if escaped {
            if c != '\n' {
                current.push(c);
            }
            escaped = false;
            continue;
        }
        match c {
            '\\' => escaped = true,
            '$' if chars.peek() == Some(&'$') => {
                current.push('$');
                chars.next();
            }
            ':' if !saw_colon => {
                if !current.is_empty() {
                    out.push(std::mem::take(&mut current));
                }
                saw_colon = true;
            }
            c if c.is_whitespace() => {
                if !current.is_empty() {
                    out.push(std::mem::take(&mut current));
                }
            }
            c => current.push(c),
        }
    }
    if escaped {
        return Err("unterminated escape in dependency output".into());
    }
    if !current.is_empty() {
        out.push(current);
    }
    if !saw_colon {
        return Err("malformed compiler dependency output".into());
    }
    Ok(out)
}

fn validate_config(config: &Config, use_for: ConfigUse) -> Result<(), String> {
    if config.schema != SCHEMA {
        return Err(format!("unsupported import schema {}", config.schema));
    }
    if CTarget::from_name(&config.target).is_none() {
        return Err(format!("unsupported compiler target `{}`", config.target));
    }
    if matches!(use_for, ConfigUse::Prepare) {
        let meta = fs::metadata(&config.compiler)
            .map_err(|e| format!("compiler {}: {e}", config.compiler.display()))?;
        if !meta.is_file() {
            return Err("compiler path is not a regular file".into());
        }
    }
    for key in config.environment.allow.keys() {
        if !matches!(
            key.as_str(),
            "PATH" | "LC_ALL" | "LANG" | "SOURCE_DATE_EPOCH"
        ) {
            return Err(format!("environment variable `{key}` is not allowlisted"));
        }
    }
    if config.sources.is_empty() || config.sources.len() > MAX_SOURCES {
        return Err("import source count is outside bounds".into());
    }
    let mut logical = HashSet::new();
    let mut paths = BTreeSet::new();
    let mut artifacts = BTreeSet::new();
    let config_identity = path_identity(&config.config_path)?;
    reject_symlink_components(&lock_path_from_config(config))?;
    let lock_identity = path_identity(&lock_path_from_config(config))?;
    for source in &config.sources {
        if source.logical_source.is_empty() || source.path.is_empty() || source.artifact.is_empty()
        {
            return Err("source logical_source, path, and artifact must be non-empty".into());
        }
        if !logical.insert(source.logical_source.clone()) {
            return Err(format!(
                "duplicate logical source {}",
                source.logical_source
            ));
        }
        validate_args(&source.args, config.c_target())?;
        let path = resolve_source(config, &source.path)?;
        let artifact = resolve_artifact(config, &source.artifact)?;
        reject_symlink_components(&artifact)?;
        let source_identity_path = path_identity(&path)?;
        let artifact_identity = path_identity(&artifact)?;
        if !paths.insert(source_identity_path.clone()) {
            return Err(format!("duplicate source path {}", path.display()));
        }
        if !artifacts.insert(artifact_identity.clone()) {
            return Err(format!("duplicate artifact path {}", artifact.display()));
        }
        if source_identity_path == artifact_identity
            || source_identity_path == lock_identity
            || artifact_identity == lock_identity
            || source_identity_path == config_identity
            || artifact_identity == config_identity
        {
            return Err("source, artifact, config, and lock paths must not overlap".into());
        }
    }
    if paths.iter().any(|path| artifacts.contains(path)) {
        return Err("a source path overlaps an artifact path".into());
    }
    Ok(())
}

fn validate_args(args: &[String], target: CTarget) -> Result<(), String> {
    if args.len() > MAX_ARGUMENTS
        || args.iter().map(String::len).sum::<usize>() > MAX_ARGUMENT_BYTES
    {
        return Err("compiler argument list exceeds bounds".into());
    }
    let profile_args = fixed_args(target);
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        if arg.is_empty() || arg.contains('\0') {
            return Err("compiler argument is empty or contains NUL".into());
        }
        if matches!(arg.as_str(), "-x" | "-E" | "-MD" | "-MF" | "-c" | "-o")
            || arg.starts_with('@')
            || arg.starts_with("-fplugin")
            || arg.starts_with("-specs")
            || arg == "-B"
            || arg == "-wrapper"
            || arg.starts_with("-Wa,")
            || arg.starts_with("-Wl,")
        {
            return Err(format!("unsupported compiler argument `{arg}`"));
        }
        if profile_args.contains(arg) {
            i += 1;
            continue;
        }
        let separate = matches!(arg.as_str(), "-D" | "-U" | "-I" | "-isystem" | "-include");
        let prefix = arg.starts_with("-D")
            || arg.starts_with("-U")
            || arg.starts_with("-I")
            || arg.starts_with("-isystem")
            || arg.starts_with("-include");
        if !prefix {
            return Err(format!(
                "unsupported compiler argument `{arg}`; only -D/-U/-I/-isystem/-include are supported"
            ));
        }
        if !separate
            && ((arg.starts_with("-isystem") && arg.len() == 8)
                || (arg.starts_with("-include") && arg.len() == 8)
                || (!arg.starts_with("-isystem") && !arg.starts_with("-include") && arg.len() == 2))
        {
            return Err(format!("missing value after `{arg}`"));
        }
        if separate {
            i += 1;
            if i == args.len() || args[i].is_empty() || args[i].contains('\0') {
                return Err(format!("missing value after `{arg}`"));
            }
            if matches!(arg.as_str(), "-D" | "-U") {
                reject_profile_define(&args[i], target)?;
            }
        } else if arg.starts_with("-D") || arg.starts_with("-U") {
            reject_profile_define(&arg[2..], target)?;
        }
        i += 1;
    }
    Ok(())
}

fn reject_profile_define(value: &str, target: CTarget) -> Result<(), String> {
    let name = value.split(['=', '(']).next().unwrap_or(value).trim();
    if target == CTarget::X86_64LinuxUserspace
        && matches!(
            name,
            "__KERNEL__"
                | "__STDC__"
                | "__STDC_VERSION__"
                | "__STRICT_ANSI__"
                | "_POSIX_C_SOURCE"
                | "_REENTRANT"
        )
    {
        return Err(format!("cannot override user-space profile macro {name}"));
    }
    if name.starts_with("__SIZEOF_")
        || name.starts_with("__ORDER_")
        || matches!(
            name,
            "__x86_64__" | "__LP64__" | "__CHAR_UNSIGNED__" | "__CHAR_BIT__" | "__BYTE_ORDER__"
        )
    {
        return Err(format!("cannot override compiler ABI macro {name}"));
    }
    Ok(())
}

fn normalize_config(config: &mut Config, use_for: ConfigUse) -> Result<(), String> {
    config.compiler = absolute_path(&config.compiler, &config.config_directory)?;
    if matches!(use_for, ConfigUse::Prepare) {
        config.compiler =
            fs::canonicalize(&config.compiler).map_err(|e| format!("resolve compiler: {e}"))?;
    }
    config.working_directory = absolute_path(
        Path::new(&config.working_directory),
        &config.config_directory,
    )?
    .to_string_lossy()
    .into_owned();
    Ok(())
}
fn explicit_roots(config: &Config) -> Result<Vec<PathBuf>, String> {
    let mut roots = BTreeSet::new();
    roots.insert(PathBuf::from(&config.working_directory));
    roots.insert(config.config_path.clone());
    for source in &config.sources {
        let source_path = resolve_source(config, &source.path)?;
        roots.insert(
            source_path
                .parent()
                .ok_or("source has no parent directory")?
                .to_path_buf(),
        );
        let mut i = 0;
        while i < source.args.len() {
            let arg = &source.args[i];
            let (kind, value) = if matches!(arg.as_str(), "-I" | "-isystem" | "-include") {
                i += 1;
                if i == source.args.len() {
                    return Err(format!("missing value after {arg}"));
                }
                (arg.as_str(), source.args[i].as_str())
            } else if let Some(v) = arg.strip_prefix("-isystem") {
                ("-isystem", v)
            } else if let Some(v) = arg.strip_prefix("-include") {
                ("-include", v)
            } else if let Some(v) = arg.strip_prefix("-I") {
                ("-I", v)
            } else {
                i += 1;
                continue;
            };
            let path = absolute_path(Path::new(value), Path::new(&config.working_directory))?;
            if kind == "-include" {
                roots.insert(path.parent().unwrap_or(Path::new("/")).to_path_buf());
            } else {
                roots.insert(path);
            }
            i += 1;
        }
    }
    Ok(roots.into_iter().collect())
}

fn canonicalize_roots(roots: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    let mut canonical = BTreeSet::new();
    for root in roots {
        reject_symlink_components(root)?;
        let path = match fs::canonicalize(root) {
            Ok(path) => path,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => root.clone(),
            Err(error) => {
                return Err(format!(
                    "canonicalize input root {}: {error}",
                    root.display()
                ));
            }
        };
        canonical.insert(path);
    }
    Ok(canonical.into_iter().collect())
}

fn output_exclusions(config: &Config) -> Result<BTreeSet<PathBuf>, String> {
    let mut result = BTreeSet::new();
    result.insert(path_identity(&lock_path_from_config(config))?);
    for source in &config.sources {
        result.insert(path_identity(&resolve_artifact(config, &source.artifact)?)?);
    }
    Ok(result)
}

fn snapshot_roots(
    roots: &[PathBuf],
    exclusions: &BTreeSet<PathBuf>,
) -> Result<RootSnapshot, String> {
    let mut entries = BTreeMap::new();
    let mut bytes = 0;
    let mut roots = roots.to_vec();
    roots.sort();
    let selected = prune_roots(roots);
    for root in selected {
        snapshot_path(&root, exclusions, &mut entries, &mut bytes, 0)?;
    }
    Ok(RootSnapshot { entries, bytes })
}

fn snapshot_path(
    path: &Path,
    exclusions: &BTreeSet<PathBuf>,
    entries: &mut BTreeMap<String, FileState>,
    bytes: &mut u64,
    depth: usize,
) -> Result<(), String> {
    check_cancelled()?;
    if depth > 128 || entries.len() >= MAX_ROOT_ENTRIES {
        return Err("input root inventory exceeds depth or entry bound".into());
    }
    if exclusions.contains(path) {
        return Ok(());
    }
    let metadata = match fs::symlink_metadata(path) {
        Ok(x) => x,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            entries.insert(
                path.to_string_lossy().into_owned(),
                FileState {
                    kind: 0,
                    len: 0,
                    modified: 0,
                    changed: 0,
                    inode: 0,
                    content_sha256: String::new(),
                },
            );
            return Ok(());
        }
        Err(e) => return Err(format!("stat input root {}: {e}", path.display())),
    };
    if metadata.is_file() && metadata.len() > MAX_ROOT_BYTES.saturating_sub(*bytes) {
        return Err("input root inventory exceeds byte bound".into());
    }
    let state = file_state(path, &metadata)?;
    *bytes = bytes.saturating_add(state.len);
    if entries.len() >= MAX_ROOT_ENTRIES {
        return Err("input root inventory exceeds entry bound".into());
    }
    if *bytes > MAX_ROOT_BYTES {
        return Err("input root inventory exceeds byte bound".into());
    }
    entries.insert(path.to_string_lossy().into_owned(), state);
    if metadata.is_dir() {
        let mut children = fs::read_dir(path)
            .map_err(|e| format!("read input root {}: {e}", path.display()))?
            .take(MAX_ROOT_ENTRIES.saturating_sub(entries.len()) + 1)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("read input root {}: {e}", path.display()))?;
        if children.len() > MAX_ROOT_ENTRIES.saturating_sub(entries.len()) {
            return Err("input root inventory exceeds entry bound".into());
        }
        children.sort_by_key(|x| x.file_name());
        for child in children {
            snapshot_path(&child.path(), exclusions, entries, bytes, depth + 1)?;
        }
    }
    Ok(())
}

fn file_state(path: &Path, metadata: &fs::Metadata) -> Result<FileState, String> {
    let kind = if metadata.is_dir() {
        2
    } else if metadata.is_file() {
        1
    } else {
        3
    };
    let content_sha256 = if metadata.is_file() {
        file_digest(path)?
    } else if metadata.file_type().is_symlink() {
        hex_digest(
            fs::read_link(path)
                .map_err(|e| format!("read link {}: {e}", path.display()))?
                .to_string_lossy()
                .as_bytes(),
        )
    } else {
        String::new()
    };
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        Ok(FileState {
            kind,
            len: metadata.len(),
            modified: (metadata.mtime() as i128 * 1_000_000_000 + metadata.mtime_nsec() as i128)
                as u128,
            changed: (metadata.ctime() as i128 * 1_000_000_000 + metadata.ctime_nsec() as i128)
                as u128,
            inode: metadata.ino(),
            content_sha256,
        })
    }
    #[cfg(not(unix))]
    {
        Ok(FileState {
            kind,
            len: metadata.len(),
            modified: metadata
                .modified()
                .ok()
                .and_then(|x| x.duration_since(std::time::UNIX_EPOCH).ok())
                .map_or(0, |x| x.as_nanos()),
            changed: 0,
            inode: 0,
            content_sha256,
        })
    }
}

fn verify_roots(context: &Context<'_>) -> Result<(), String> {
    let after = snapshot_roots(&context.roots, &context.exclusions)?;
    if after != context.before {
        return Err(
            "compiler input roots changed while preprocessing; retry after quiescing the build"
                .into(),
        );
    }
    let (toolchain, generation) = discover_toolchain(context.config)?;
    if toolchain != context.toolchain || generation != context.toolchain_generation {
        return Err(
            "compiler toolchain changed while preprocessing; retry after quiescing the build"
                .into(),
        );
    }
    Ok(())
}

fn discover_toolchain(
    config: &Config,
) -> Result<(ToolchainIdentity, BTreeMap<String, FileState>), String> {
    let driver_state = regular_file_state(&config.compiler)?;
    let driver_sha256 = driver_state.content_sha256.clone();
    let cc1 = query_compiler(config, "-print-prog-name=cc1")?;
    let cc1_path = absolute_path(Path::new(cc1.trim()), Path::new(&config.working_directory))?;
    if !cc1_path.is_file() {
        return Err(format!(
            "compiler did not identify a usable cc1: {}",
            cc1.trim()
        ));
    }
    let cc1_state = regular_file_state(&cc1_path)?;
    let mut generation = BTreeMap::new();
    generation.insert(
        config.compiler.to_string_lossy().into_owned(),
        driver_state.clone(),
    );
    generation.insert(cc1_path.to_string_lossy().into_owned(), cc1_state.clone());
    let include = query_compiler(config, "-print-file-name=include")?;
    let include = absolute_path(
        Path::new(include.trim()),
        Path::new(&config.working_directory),
    )?;
    let mut resource_files = BTreeMap::new();
    if include.is_dir() {
        for (path, state) in snapshot_roots(&[include], &BTreeSet::new())?.entries {
            if state.kind == 1 {
                resource_files.insert(path.clone(), state.content_sha256.clone());
            }
            generation.insert(path, state);
        }
    }
    let specs = query_compiler(config, "-print-file-name=specs")?;
    let specs_path = if specs.trim() == "specs" || specs.trim().is_empty() {
        None
    } else {
        Some(
            absolute_path(
                Path::new(specs.trim()),
                Path::new(&config.working_directory),
            )?
            .to_string_lossy()
            .into_owned(),
        )
    };
    let specs_sha256 = specs_path
        .as_ref()
        .map(|x| file_digest(Path::new(x)))
        .transpose()?;
    if specs_path.is_some() {
        return Err(
            "active GCC specs files are unsupported; use the default toolchain specs".into(),
        );
    }
    let abi_probe_sha256 = abi_probe(config)?;
    if regular_file_state(&config.compiler)? != driver_state
        || regular_file_state(&cc1_path)? != cc1_state
    {
        return Err("compiler toolchain changed while identifying it".into());
    }
    Ok((
        ToolchainIdentity {
            driver_sha256,
            cc1_path: cc1_path.to_string_lossy().into_owned(),
            cc1_sha256: cc1_state.content_sha256,
            resource_files,
            specs_path,
            specs_sha256,
            abi_probe_sha256,
        },
        generation,
    ))
}

fn regular_file_state(path: &Path) -> Result<FileState, String> {
    let metadata = fs::metadata(path).map_err(|e| format!("stat compiler input: {e}"))?;
    if !metadata.is_file() {
        return Err("compiler input is not a regular file".into());
    }
    file_state(path, &metadata)
}

fn query_compiler(config: &Config, arg: &str) -> Result<String, String> {
    let output = run_compiler(
        &config.compiler,
        &[arg.into()],
        Path::new(&config.working_directory),
        &config.environment.allow,
        limits(),
    )?;
    if !output.stderr.is_empty() {
        return Err(format!(
            "compiler identity query diagnostics: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|e| format!("compiler identity query was not UTF-8: {e}"))
}
fn abi_probe(config: &Config) -> Result<String, String> {
    let path = unique_temp_path("click-import-abi", ".c")?;
    let _cleanup = RemoveFile(path.clone());
    atomic_write(&path, b"int click_import_abi_probe;\n")?;
    let mut args = fixed_args(config.c_target());
    args.extend([
        "-dM".into(),
        "-E".into(),
        "-x".into(),
        "c".into(),
        path.to_string_lossy().into_owned(),
    ]);
    let output = run_compiler(
        &config.compiler,
        &args,
        Path::new(&config.working_directory),
        &config.environment.allow,
        limits(),
    );
    let _ = fs::remove_file(&path);
    let output = output?;
    let macros = String::from_utf8(output.stdout)
        .map_err(|e| format!("ABI probe output was not UTF-8: {e}"))?;
    for expected in [
        "#define __x86_64__ 1",
        "#define __LP64__ 1",
        "#define __CHAR_UNSIGNED__ 1",
        "#define __CHAR_BIT__ 8",
        "#define __SIZEOF_SHORT__ 2",
        "#define __SIZEOF_INT__ 4",
        "#define __SIZEOF_LONG__ 8",
        "#define __SIZEOF_LONG_LONG__ 8",
        "#define __SIZEOF_POINTER__ 8",
        "#define __BYTE_ORDER__ __ORDER_LITTLE_ENDIAN__",
    ] {
        if !macros.lines().any(|line| line.trim() == expected) {
            return Err(format!("compiler ABI probe did not establish {expected}"));
        }
    }
    if config.c_target() == CTarget::X86_64LinuxUserspace {
        for expected in [
            "#define __STDC_VERSION__ 201112L",
            "#define __STRICT_ANSI__ 1",
            "#define _POSIX_C_SOURCE 200809L",
            "#define _REENTRANT 1",
        ] {
            if !macros.lines().any(|line| line.trim() == expected) {
                return Err(format!(
                    "compiler user-space probe did not establish {expected}"
                ));
            }
        }
        if macros
            .lines()
            .any(|line| line.starts_with("#define __KERNEL__ "))
        {
            return Err("compiler user-space probe unexpectedly defines __KERNEL__".into());
        }
    }
    Ok(hex_digest(macros.as_bytes()))
}

fn lock_path(config_path: &Path) -> PathBuf {
    let name = config_path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("import.json")
        .trim_end_matches(".json");
    config_path.with_file_name(format!("{name}.lock.json"))
}
fn lock_path_from_config(config: &Config) -> PathBuf {
    config.lock_path.clone()
}
fn resolve_source(config: &Config, path: &str) -> Result<PathBuf, String> {
    absolute_path(Path::new(path), Path::new(&config.working_directory))
}
fn resolve_artifact(config: &Config, path: &str) -> Result<PathBuf, String> {
    absolute_path(Path::new(path), &config.config_directory)
}
// Root aliases could change while their canonical target snapshot stayed
// fixed. This first profile rejects them, including symlinks before `..`.
fn reject_symlink_components(path: &Path) -> Result<(), String> {
    let mut prefix = PathBuf::new();
    for component in path.components() {
        prefix.push(component.as_os_str());
        match fs::symlink_metadata(&prefix) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(format!(
                    "symlinked import roots or outputs are unsupported: {}",
                    prefix.display()
                ));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(format!("inspect import path: {error}")),
        }
    }
    Ok(())
}

fn path_identity(path: &Path) -> Result<PathBuf, String> {
    match fs::canonicalize(path) {
        Ok(path) => Ok(path),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let parent = path
                .parent()
                .ok_or_else(|| format!("path {} has no parent", path.display()))?;
            let parent = fs::canonicalize(parent)
                .map_err(|e| format!("canonicalize parent {}: {e}", parent.display()))?;
            Ok(parent.join(
                path.file_name()
                    .ok_or_else(|| format!("path {} has no filename", path.display()))?,
            ))
        }
        Err(error) => Err(format!("canonicalize {}: {error}", path.display())),
    }
}
fn absolute_path(path: &Path, base: &Path) -> Result<PathBuf, String> {
    if path.as_os_str().is_empty() {
        return Err("empty path".into());
    }
    let base = if base.is_absolute() {
        base.to_path_buf()
    } else {
        std::env::current_dir()
            .map_err(|e| format!("resolve current directory: {e}"))?
            .join(base)
    };
    let joined = if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    };
    // Preserve `..` for the filesystem: collapsing it lexically changes the
    // meaning of paths that cross a symlink. The compiler receives source.path
    // verbatim; absolute paths here are used for validation only.
    Ok(joined)
}

fn limits() -> CompilerLimits {
    CompilerLimits {
        timeout: Duration::from_secs(30),
        max_stdout_bytes: MAX_ARTIFACT_BYTES,
        max_stderr_bytes: 2 << 20,
    }
}
fn invocation_digest(config: &Config, toolchain: &ToolchainIdentity) -> String {
    invocation_digest_parts(
        &config.target,
        &config.compiler.to_string_lossy(),
        &config.working_directory,
        &config.environment.allow,
        toolchain,
    )
}

fn invocation_digest_parts(
    target: &str,
    compiler_path: &str,
    working_directory: &str,
    environment: &BTreeMap<String, String>,
    toolchain: &ToolchainIdentity,
) -> String {
    let mut bytes = serde_json::to_vec(&(
        target,
        compiler_path,
        working_directory,
        environment,
        toolchain,
    ))
    .expect("identity serializes");
    let target = CTarget::from_name(target).expect("validated compiler target");
    bytes.extend_from_slice(fixed_args(target).join("\0").as_bytes());
    hex_digest(&bytes)
}
fn unique_temp_path(prefix: &str, suffix: &str) -> Result<PathBuf, String> {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| format!("clock: {e}"))?
        .as_nanos();
    let path =
        std::env::temp_dir().join(format!("{prefix}-{}-{nanos}{suffix}", std::process::id()));
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .map_err(|e| format!("reserve temporary compiler input: {e}"))?;
    Ok(path)
}
fn atomic_write(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let parent = path.parent().unwrap_or(Path::new("."));
    fs::create_dir_all(parent)
        .map_err(|e| format!("create directory {}: {e}", parent.display()))?;
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| format!("clock: {e}"))?
        .as_nanos();
    let temp = parent.join(format!(".click-import-{}-{nanos}.tmp", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temp)
        .map_err(|e| format!("create temporary output: {e}"))?;
    let _cleanup = RemoveFile(temp.clone());
    file.write_all(bytes)
        .map_err(|e| format!("write temporary output: {e}"))?;
    file.sync_all()
        .map_err(|e| format!("sync temporary output: {e}"))?;
    drop(file);
    fs::rename(&temp, path).map_err(|e| {
        let _ = fs::remove_file(&temp);
        format!("install {}: {e}", path.display())
    })
}
fn read_bounded(path: &Path, max: usize, label: &str) -> Result<Vec<u8>, String> {
    let file = open_regular(path, label)?;
    let mut bytes = Vec::new();
    file.take(max as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("read {label}: {e}"))?;
    if bytes.len() > max {
        return Err(format!("{label} exceeds {max} bytes"));
    }
    Ok(bytes)
}
fn read_stable(path: &Path, max: usize, label: &str) -> Result<Vec<u8>, String> {
    let before =
        fs::symlink_metadata(path).map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
    let bytes = read_bounded(path, max, label)?;
    let after =
        fs::symlink_metadata(path).map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
    if metadata_signature(&before) != metadata_signature(&after) {
        return Err(format!("{label} changed while being read"));
    }
    Ok(bytes)
}
fn metadata_signature(metadata: &fs::Metadata) -> (u64, u128, u128, u64) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        (
            metadata.len(),
            (metadata.mtime() as i128 * 1_000_000_000 + metadata.mtime_nsec() as i128) as u128,
            (metadata.ctime() as i128 * 1_000_000_000 + metadata.ctime_nsec() as i128) as u128,
            metadata.ino(),
        )
    }
    #[cfg(not(unix))]
    {
        (
            metadata.len(),
            metadata
                .modified()
                .ok()
                .and_then(|x| x.duration_since(std::time::UNIX_EPOCH).ok())
                .map_or(0, |x| x.as_nanos()),
            0,
            0,
        )
    }
}
fn validate_lock_shape(lock: &Lock, config: &Config) -> Result<(), String> {
    if lock.schema != LOCK_SCHEMA || lock.target != config.target {
        return Err("import lock schema or target does not match config".into());
    }
    if lock.sources.len() != config.sources.len() {
        return Err("import lock source count does not match config".into());
    }
    let mut names = HashSet::new();
    for source in &lock.sources {
        if !names.insert(&source.logical_source) {
            return Err(format!("duplicate lock source {}", source.logical_source));
        }
    }
    Ok(())
}
fn reject_duplicate_json_keys(bytes: &[u8]) -> Result<(), String> {
    let text = std::str::from_utf8(bytes).map_err(|e| format!("JSON is not UTF-8: {e}"))?;
    let mut parser = JsonKeys {
        text,
        pos: 0,
        depth: 0,
    };
    parser.value()?;
    parser.ws();
    if parser.pos != text.len() {
        return Err("trailing data after JSON value".into());
    }
    Ok(())
}
struct JsonKeys<'a> {
    text: &'a str,
    pos: usize,
    depth: usize,
}
impl<'a> JsonKeys<'a> {
    fn ws(&mut self) {
        while self.pos < self.text.len() {
            let c = self.text.as_bytes()[self.pos];
            if !matches!(c, b' ' | b'\n' | b'\r' | b'\t') {
                break;
            }
            self.pos += 1;
        }
    }
    fn value(&mut self) -> Result<(), String> {
        self.ws();
        let c = *self
            .text
            .as_bytes()
            .get(self.pos)
            .ok_or("unexpected end of JSON")?;
        if self.depth >= 64 {
            return Err("import JSON exceeds nesting bound".into());
        }
        match c {
            b'{' | b'[' => {
                self.depth += 1;
                let result = if c == b'{' {
                    self.object()
                } else {
                    self.array()
                };
                self.depth -= 1;
                result
            }
            b'"' => {
                self.string()?;
                Ok(())
            }
            b't' | b'f' | b'n' | b'-' | b'0'..=b'9' => {
                while self.pos < self.text.len()
                    && !matches!(
                        self.text.as_bytes()[self.pos],
                        b',' | b']' | b'}' | b' ' | b'\n' | b'\r' | b'\t'
                    )
                {
                    self.pos += 1;
                }
                Ok(())
            }
            _ => Err(format!("invalid JSON at byte {}", self.pos)),
        }
    }
    fn string(&mut self) -> Result<String, String> {
        if self.text.as_bytes().get(self.pos) != Some(&b'"') {
            return Err("expected JSON string".into());
        }
        self.pos += 1;
        let start = self.pos;
        let mut escaped = false;
        while self.pos < self.text.len() {
            let c = self.text.as_bytes()[self.pos] as char;
            self.pos += 1;
            if escaped {
                escaped = false;
                continue;
            }
            if c == '\\' {
                escaped = true;
                continue;
            }
            if c == '"' {
                return serde_json::from_str(&format!("\"{}\"", &self.text[start..self.pos - 1]))
                    .map_err(|e| format!("invalid JSON string: {e}"));
            }
        }
        Err("unterminated JSON string".into())
    }
    fn object(&mut self) -> Result<(), String> {
        self.pos += 1;
        self.ws();
        let mut keys = HashSet::new();
        if self.text.as_bytes().get(self.pos) == Some(&b'}') {
            self.pos += 1;
            return Ok(());
        }
        loop {
            self.ws();
            let key = self.string()?;
            if !keys.insert(key) {
                return Err("duplicate JSON object key".into());
            }
            self.ws();
            if self.text.as_bytes().get(self.pos) != Some(&b':') {
                return Err("expected ':' in JSON object".into());
            }
            self.pos += 1;
            self.value()?;
            self.ws();
            match self.text.as_bytes().get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b'}') => {
                    self.pos += 1;
                    return Ok(());
                }
                _ => return Err("expected ',' or '}' in JSON object".into()),
            }
        }
    }
    fn array(&mut self) -> Result<(), String> {
        self.pos += 1;
        self.ws();
        if self.text.as_bytes().get(self.pos) == Some(&b']') {
            self.pos += 1;
            return Ok(());
        }
        loop {
            self.value()?;
            self.ws();
            match self.text.as_bytes().get(self.pos) {
                Some(b',') => self.pos += 1,
                Some(b']') => {
                    self.pos += 1;
                    return Ok(());
                }
                _ => return Err("expected ',' or ']' in JSON array".into()),
            }
        }
    }
}
fn file_digest(path: &Path) -> Result<String, String> {
    let mut file = open_regular(path, "input")?;
    if file.metadata().map_err(|e| e.to_string())?.len() > MAX_ROOT_BYTES {
        return Err("input file exceeds byte bound".into());
    }
    let mut digest = Sha256::new();
    let mut count = 0u64;
    let mut buffer = [0u8; 65536];
    loop {
        check_cancelled()?;
        let n = file
            .read(&mut buffer)
            .map_err(|e| format!("read input: {e}"))?;
        if n == 0 {
            break;
        }
        count += n as u64;
        if count > MAX_ROOT_BYTES {
            return Err("input file exceeds byte bound".into());
        }
        digest.update(&buffer[..n]);
    }
    Ok(format!("{:x}", digest.finalize()))
}

struct RemoveFile(PathBuf);
impl Drop for RemoveFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn charge_artifact_bytes(total: &mut usize, bytes: usize) -> Result<(), String> {
    if bytes > MAX_PROJECT_ARTIFACT_BYTES.saturating_sub(*total) {
        return Err("combined compiler artifacts exceed project byte bound".into());
    }
    *total += bytes;
    Ok(())
}

fn open_regular(path: &Path, label: &str) -> Result<File, String> {
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.custom_flags(libc::O_NONBLOCK);
    }
    let file = options
        .open(path)
        .map_err(|e| format!("read {label} {}: {e}", path.display()))?;
    if !file.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err(format!("{label} must be a regular file"));
    }
    Ok(file)
}

fn check_cancelled() -> Result<(), String> {
    if crate::instrumentation::deadline_exceeded() {
        Err("compiler import cancelled or exceeded its deadline".into())
    } else {
        Ok(())
    }
}

fn bounded_error(mut message: String) -> String {
    const LIMIT: usize = 16 * 1024;
    if message.len() > LIMIT {
        let mut end = LIMIT - 40;
        while !message.is_char_boundary(end) {
            end -= 1;
        }
        message.truncate(end);
        message.push_str("\n[import diagnostic truncated]");
    }
    message
}

fn root_contains(roots: &[PathBuf], path: &Path) -> bool {
    path.ancestors().any(|ancestor| {
        roots
            .binary_search_by(|root| root.as_path().cmp(ancestor))
            .is_ok()
    })
}

fn prune_roots(roots: Vec<PathBuf>) -> Vec<PathBuf> {
    let mut selected: Vec<PathBuf> = Vec::new();
    for root in roots {
        if selected
            .last()
            .is_none_or(|parent| !root.starts_with(parent))
        {
            selected.push(root);
        }
    }
    selected
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct OfflineFixture {
        root: PathBuf,
    }

    impl OfflineFixture {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let root = fs::canonicalize(std::env::temp_dir())
                .unwrap()
                .join(format!(
                    "click-c-offline-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
            fs::create_dir(&root).unwrap();
            let source = b"#include \"local.h\"\nint answer(void) { return VALUE; }\n";
            let header = b"#define VALUE 42\n";
            let artifact = b"int answer(void) { return 42; }\n";
            fs::write(root.join("main.c"), source).unwrap();
            fs::write(root.join("local.h"), header).unwrap();
            fs::write(root.join("main.i"), artifact).unwrap();
            fs::write(
                root.join("main.click"),
                "verifying \"main.c\"; int answer() { ensures result == 42; } by { execute(); simp(); }",
            )
            .unwrap();
            let config = serde_json::json!({
                "schema": SCHEMA,
                "target": "x86_64-linux-kernel",
                "compiler": "/toolchain/not-installed/gcc",
                "working_directory": ".",
                "environment": {"allow": {}},
                "sources": [{
                    "logical_source": "main.c",
                    "path": "main.c",
                    "args": [],
                    "artifact": "main.i"
                }]
            });
            let config_path = root.join("main.click.import.json");
            let config_bytes = serde_json::to_vec(&config).unwrap();
            fs::write(&config_path, &config_bytes).unwrap();
            let (parsed, _) = read_config(&config_path, ConfigUse::Load).unwrap();
            let toolchain = ToolchainIdentity {
                driver_sha256: hex_digest(b"gcc"),
                cc1_path: "/toolchain/not-installed/cc1".to_string(),
                cc1_sha256: hex_digest(b"cc1"),
                resource_files: BTreeMap::new(),
                specs_path: None,
                specs_sha256: None,
                abi_probe_sha256: hex_digest(b"abi"),
            };
            let compiler_path = "/toolchain/not-installed/gcc".to_string();
            let working_directory = root.to_string_lossy().into_owned();
            let invocation_sha256 = invocation_digest_parts(
                &parsed.target,
                &compiler_path,
                &working_directory,
                &parsed.environment.allow,
                &toolchain,
            );
            let source_sha256 = hex_digest(source);
            let artifact_sha256 = hex_digest(artifact);
            let dependencies =
                BTreeMap::from([("/toolchain/include/local.h".to_string(), hex_digest(header))]);
            let source_config = &parsed.sources[0];
            let locked = LockedSource {
                logical_source: source_config.logical_source.clone(),
                path: source_config.path.clone(),
                args: source_config.args.clone(),
                artifact: source_config.artifact.clone(),
                source_sha256: source_sha256.clone(),
                artifact_sha256: artifact_sha256.clone(),
                artifact_bytes: artifact.len(),
                dependencies: dependencies.clone(),
                local_dependencies: BTreeMap::from([("local.h".to_string(), hex_digest(header))]),
                identity: source_identity_parts(
                    &parsed.target,
                    &invocation_sha256,
                    source_config,
                    &source_sha256,
                    &dependencies,
                    &BTreeMap::from([("local.h".to_string(), hex_digest(header))]),
                    &artifact_sha256,
                ),
            };
            let lock = Lock {
                schema: LOCK_SCHEMA,
                config_sha256: hex_digest(&config_bytes),
                target: parsed.target,
                compiler_path,
                working_directory,
                config_directory: "/toolchain/include".to_string(),
                invocation_sha256,
                toolchain,
                sources: vec![locked],
            };
            fs::write(lock_path(&config_path), serde_json::to_vec(&lock).unwrap()).unwrap();
            Self { root }
        }

        fn config(&self) -> PathBuf {
            self.root.join("main.click.import.json")
        }
    }

    impl Drop for OfflineFixture {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn locked_c_import_verifies_without_the_target_compiler_or_headers() {
        let fixture = OfflineFixture::new();
        let proof = fs::read_to_string(fixture.root.join("main.click")).unwrap();
        let crate::cli::CInput::Prepared(imports) =
            crate::cli::read_c_inputs(&fixture.root.join("main.click"), &proof).unwrap()
        else {
            panic!("the ordinary CLI input path must load the prepared C artifact");
        };
        assert_eq!(imports[0].source(), "int answer(void) { return 42; }\n");
        crate::surface::verify_c0_prepared_sources(&proof, &imports).unwrap();

        let relocated = OfflineFixture::new();
        fs::copy(lock_path(&fixture.config()), lock_path(&relocated.config())).unwrap();
        let same = load_imports(&relocated.config()).unwrap();
        assert_eq!(same[0].identity(), imports[0].identity());
        crate::surface::verify_c0_prepared_sources(&proof, &same).unwrap();
    }

    #[test]
    fn locked_c_import_rejects_changed_source_artifact_and_local_header() {
        let fixture = OfflineFixture::new();
        let source = fixture.root.join("main.c");
        let artifact = fixture.root.join("main.i");
        let header = fixture.root.join("local.h");
        for (path, replacement) in [
            (&source, "int answer(void) { return 43; }\n"),
            (&artifact, "int answer(void) { return 43; }\n"),
            (&header, "#define VALUE 43\n"),
        ] {
            let original = fs::read(path).unwrap();
            fs::write(path, replacement).unwrap();
            assert!(load_imports(&fixture.config()).is_err());
            fs::write(path, original).unwrap();
        }
        assert!(load_imports(&fixture.config()).is_ok());
        let lock_file = lock_path(&fixture.config());
        let original_lock = fs::read(&lock_file).unwrap();
        for field in ["toolchain", "local_dependencies"] {
            let mut altered: serde_json::Value = serde_json::from_slice(&original_lock).unwrap();
            if field == "toolchain" {
                altered["toolchain"]["driver_sha256"] = serde_json::json!(hex_digest(b"other"));
            } else {
                altered["sources"][0]["local_dependencies"] = serde_json::json!({});
            }
            fs::write(&lock_file, serde_json::to_vec(&altered).unwrap()).unwrap();
            assert!(load_imports(&fixture.config()).is_err(), "altered {field}");
        }
        fs::write(&lock_file, original_lock).unwrap();
        assert!(load_imports(&fixture.config()).is_ok());
    }

    #[test]
    fn rejects_ambient_or_executable_compiler_options() {
        assert!(validate_args(&["-fplugin=evil.so".into()], CTarget::SUPPORTED).is_err());
        assert!(validate_args(&["-c".into()], CTarget::SUPPORTED).is_err());
        assert!(validate_args(&["@args.rsp".into()], CTarget::SUPPORTED).is_err());
    }

    #[test]
    fn accepts_ordered_profile_arguments() {
        validate_args(
            &[
                "-nostdinc".into(),
                "-m64".into(),
                "-funsigned-char".into(),
                "-std=gnu11".into(),
                "-D".into(),
                "FLAG=1".into(),
                "-Iinclude".into(),
                "-isystem".into(),
                "/usr/include".into(),
                "-include".into(),
                "config.h".into(),
            ],
            CTarget::SUPPORTED,
        )
        .unwrap();
    }

    #[test]
    fn dependency_lexer_preserves_escaped_spaces() {
        assert_eq!(
            dep_tokens("x.o: a\\ b.h c\\#d.h\\\n next.h\n").unwrap(),
            vec!["x.o", "a b.h", "c#d.h", "next.h"]
        );
    }

    #[test]
    fn duplicate_json_keys_are_rejected() {
        assert!(reject_duplicate_json_keys(br#"{"a":1,"a":2}"#).is_err());
        assert!(reject_duplicate_json_keys(br#"{"a":[{"b":1,"b":2}]}"#).is_err());
    }

    #[test]
    fn relative_paths_are_anchored_to_the_process_directory() {
        let resolved = absolute_path(Path::new("Cargo.toml"), Path::new(".")).unwrap();
        assert!(resolved.is_absolute());
        assert!(resolved.ends_with("Cargo.toml"));
    }

    #[cfg(unix)]
    #[test]
    fn dependency_symlink_escape_is_rejected() {
        let root =
            std::env::temp_dir().join(format!("click-import-symlink-{}", std::process::id()));
        let outside =
            std::env::temp_dir().join(format!("click-import-outside-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        let _ = fs::remove_file(&outside);
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("x.c"), b"source").unwrap();
        fs::write(&outside, b"outside").unwrap();
        std::os::unix::fs::symlink(&outside, root.join("escape.h")).unwrap();
        let dep = format!("x.o: {}\n", root.join("escape.h").display());
        let roots = vec![fs::canonicalize(&root).unwrap()];
        assert!(
            parse_dependencies(
                dep.as_bytes(),
                &root.join("x.c"),
                ".",
                &roots,
                &BTreeSet::new()
            )
            .is_err()
        );
        let _ = fs::remove_dir_all(&root);
        let _ = fs::remove_file(&outside);
    }

    // macOS `/usr/bin/gcc` is Apple Clang and has no GNU `cc1` executable.
    #[cfg(not(target_os = "macos"))]
    #[test]
    fn real_gcc_round_trip_uses_fixed_c_profile() {
        let root = std::env::temp_dir().join(format!("click-import-test-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("x.c"),
            b"#define VALUE 7\nint imported = VALUE;\nconst char *source_file = __FILE__;\n",
        )
        .unwrap();
        let config = format!(
            r#"{{"schema":1,"target":"x86_64-linux-kernel","compiler":"{}","working_directory":".","environment":{{"allow":{{"PATH":"{}"}}}},"sources":[{{"logical_source":"x","path":"x.c","args":[],"artifact":"x.i"}}]}}"#,
            "/usr/bin/gcc",
            std::env::var("PATH").unwrap_or_default()
        );
        let config_path = root.join("sidecar.click.import.json");
        fs::write(&config_path, config).unwrap();
        create_lock(&config_path).unwrap();
        let imports = load_imports(&config_path).unwrap();
        assert!(imports[0].source().contains("imported = 7"));
        assert!(imports[0].source().contains("source_file = \"x.c\""));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn malformed_inputs_and_diagnostics_remain_bounded() {
        let nested = format!("{}0{}", "[".repeat(1000), "]".repeat(1000));
        assert!(
            reject_duplicate_json_keys(nested.as_bytes())
                .unwrap_err()
                .contains("nesting")
        );
        assert!(bounded_error("é".repeat(20000)).len() <= 16 * 1024);
        assert_eq!(
            dep_tokens("x.o: dollar$$.h\n").unwrap(),
            vec!["x.o", "dollar$.h"]
        );
    }

    #[cfg(unix)]
    #[test]
    fn nonregular_inputs_and_cancelled_snapshots_fail_promptly() {
        use std::os::unix::ffi::OsStrExt;
        let path = std::env::temp_dir().join(format!("click-import-fifo-{}", std::process::id()));
        let _cleanup = RemoveFile(path.clone());
        let name = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        assert!(
            read_bounded(&path, 64, "config")
                .unwrap_err()
                .contains("regular")
        );
        assert!(file_digest(&path).unwrap_err().contains("regular"));
        let cancelled = crate::instrumentation::with_deadline(Duration::ZERO, || {
            snapshot_roots(&[path], &BTreeSet::new())
        });
        assert!(cancelled.unwrap_err().contains("deadline"));
    }

    #[test]
    fn root_inventory_scales_once_per_selected_file() {
        let root =
            std::env::temp_dir().join(format!("click-import-root-scaling-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        for size in [16usize, 32, 64, 128] {
            let input = root.join(format!("n{size}"));
            fs::create_dir(&input).unwrap();
            let mut roots = vec![input.clone()];
            for index in 0..size {
                let dir = input.join(format!("d{index:04}"));
                fs::create_dir(&dir).unwrap();
                let file = dir.join("input.h");
                fs::write(&file, "#define VALUE 1\n").unwrap();
                roots.push(dir);
                roots.push(file);
            }
            roots.sort();
            let compact = snapshot_roots(std::slice::from_ref(&input), &BTreeSet::new()).unwrap();
            let overlapping = snapshot_roots(&roots, &BTreeSet::new()).unwrap();
            assert_eq!(compact.entries.len(), 2 * size + 1);
            assert_eq!(
                overlapping, compact,
                "overlapping roots must not rehash selected files"
            );
            assert_eq!(prune_roots(roots.clone()), vec![input.clone()]);
            assert!(root_contains(&roots, &input.join("d0000/input.h")));
            assert!(!root_contains(&roots, &root.join("outside.h")));
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn lock_name_preserves_import_suffix() {
        assert_eq!(
            lock_path(Path::new("demo.click.import.json")),
            PathBuf::from("demo.click.import.lock.json")
        );
    }
}
