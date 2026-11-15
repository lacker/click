//! Strict, reproducible compiler-backed C imports.
//!
//! This module owns the declarative import/lock format.  Process ownership is
//! deliberately delegated to `compiler_process`; this layer validates the
//! invocation and states dependencies during explicit refresh. Ordinary
//! loading checks the recorded artifact without running the compiler.

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs::{self, OpenOptions};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::option_profile::OptionProfile;
use super::provenance::CSourceMap;
use super::syntax::PromiseAttributes;
use super::system_headers::{self, HeaderKind};
use super::target::{COptimization, CTarget};
use crate::cli::write_file_atomically;
use crate::languages::compiler_process::{CompilerLimits, run_compiler};
use crate::languages::envelope::{self, Entry, SourceParts};
use crate::languages::inputs::{
    Leaf, hex_digest, open_regular, path_identity, read_regular, read_stable,
};

const SCHEMA: u32 = 1;
const LOCK_SCHEMA: u32 = 3;
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
    promises: PromiseAttributes,
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
    /// Whether the frontend accepts GCC's optimizer-promise attributes in
    /// this import: refused when its option profile accepts optimization.
    pub fn promise_attributes(&self) -> PromiseAttributes {
        self.inner.promises
    }

    /// This import under the name a sidecar's `verifying` declaration gives
    /// it; a project unit's source is named by its path in the unit.
    pub(crate) fn named(&self, logical_source: &str) -> Self {
        if self.logical_source() == logical_source {
            return self.clone();
        }
        Self {
            inner: Arc::new(PreparedInner {
                target: self.inner.target,
                logical_source: logical_source.to_string(),
                source: self.inner.source.clone(),
                source_map: self.inner.source_map.clone(),
                identity: self.inner.identity.clone(),
                promises: self.inner.promises,
            }),
        }
    }

    #[cfg(test)]
    pub(crate) fn for_test(logical_source: &str, source: &str) -> Self {
        Self::for_test_with(logical_source, source, PromiseAttributes::Accept)
    }

    #[cfg(test)]
    pub(crate) fn for_test_on(target: CTarget, logical_source: &str, source: &str) -> Self {
        let mut import = Self::for_test(logical_source, source);
        Arc::get_mut(&mut import.inner)
            .expect("a fresh test import is unshared")
            .target = target;
        import
    }

    #[cfg(test)]
    pub(crate) fn for_test_with(
        logical_source: &str,
        source: &str,
        promises: PromiseAttributes,
    ) -> Self {
        let (source, source_map) = CSourceMap::decode(source).expect("test source map");
        Self {
            inner: Arc::new(PreparedInner {
                target: CTarget::SUPPORTED,
                logical_source: logical_source.to_string(),
                source,
                source_map,
                identity: format!("test-{logical_source}"),
                promises,
            }),
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct Config {
    schema: u32,
    #[serde(skip, default = "default_target")]
    target: CTarget,
    /// The project's optimization level, which every source is prepared for.
    #[serde(skip)]
    optimization: COptimization,
    compiler: PathBuf,
    working_directory: String,
    environment: Environment,
    /// A named compiler-option profile; see `option_profile`. Omitted, only
    /// the preprocessing options and the target's fixed arguments are
    /// accepted.
    #[serde(default)]
    option_profile: Option<String>,
    sources: Vec<SourceConfig>,
    #[serde(skip)]
    config_directory: PathBuf,
    #[serde(skip)]
    lock_path: PathBuf,
    #[serde(skip)]
    config_path: PathBuf,
    #[serde(skip)]
    config_bytes_sha256: String,
    /// Where this configuration came from: a per-sidecar import file, or a
    /// unit of `click.project.json`.
    #[serde(skip)]
    origin: ConfigOrigin,
    /// A project unit's source root when it lies outside the project
    /// directory, so its files are rechecked as the project's own are.
    #[serde(skip)]
    unit_directory: Option<PathBuf>,
}

#[derive(Clone, Debug, Default)]
enum ConfigOrigin {
    #[default]
    File,
    ProjectUnit(String),
}

fn default_target() -> CTarget {
    CTarget::SUPPORTED
}

impl Config {
    fn c_target(&self) -> CTarget {
        self.target
    }

    // Likewise, a configured profile name was resolved by validate_config.
    fn profile(&self) -> Option<&'static OptionProfile> {
        self.option_profile.as_deref().map(|name| {
            OptionProfile::named(name, self.c_target()).expect("validated option profile")
        })
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
    /// `"dependency-closure"` imports only the declarations the unit's own
    /// function definitions depend on; see `projection`. Omitted, the whole
    /// translation unit is imported.
    #[serde(default)]
    projection: Option<String>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Lock {
    schema: u32,
    config_sha256: String,
    target: String,
    /// The target's mode; absent from a lock prepared before targets were
    /// spelled as a triple and a mode.
    #[serde(default)]
    mode: String,
    compiler_path: String,
    working_directory: String,
    config_directory: String,
    invocation_sha256: String,
    /// The configured option profile, recorded beside the full argument
    /// vectors it admitted.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    option_profile: Option<String>,
    /// [`system_headers::catalog_digest`] of the Click header set the
    /// compiler searched; a lock without it is refused.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    click_header_catalog_sha256: Option<String>,
    /// A project unit's source root at preparation, when it lies outside
    /// `config_directory`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    unit_directory: Option<String>,
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
    /// Dependencies under the lock's `unit_directory`, relative to it.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    unit_dependencies: BTreeMap<String, String>,
    /// The Click system headers the compiler opened, by header name, with
    /// the SHA-256 of the text it read.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    click_headers: BTreeMap<String, String>,
}

/// A C unit's section of its project lock entry: what the envelope's common
/// fields do not record (`crate::languages::envelope`).
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Section {
    schema: u32,
    target: String,
    mode: String,
    compiler_path: String,
    working_directory: String,
    config_directory: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    option_profile: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    click_header_catalog_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    unit_directory: Option<String>,
    toolchain: ToolchainIdentity,
    sources: Vec<SectionSource>,
}

/// One source's part of a C unit's section, in the unit's source order.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SectionSource {
    logical_source: String,
    path: String,
    args: Vec<String>,
    local_dependencies: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    unit_dependencies: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    click_headers: BTreeMap<String, String>,
}

const LANGUAGE: &str = "c";

/// The envelope entry recording `lock`. A source's inputs are its own digest,
/// keyed by its path, and the digests of the headers the compiler opened.
fn lock_entry(lock: &Lock) -> Entry {
    let sources = lock
        .sources
        .iter()
        .map(|locked| {
            let mut inputs = locked.dependencies.clone();
            inputs.insert(locked.path.clone(), locked.source_sha256.clone());
            (
                locked.logical_source.clone(),
                SourceParts {
                    inputs,
                    artifact: envelope::Artifact {
                        path: locked.artifact.clone(),
                        sha256: locked.artifact_sha256.clone(),
                        bytes: locked.artifact_bytes,
                    },
                },
            )
        })
        .collect();
    let section = Section {
        schema: lock.schema,
        target: lock.target.clone(),
        mode: lock.mode.clone(),
        compiler_path: lock.compiler_path.clone(),
        working_directory: lock.working_directory.clone(),
        config_directory: lock.config_directory.clone(),
        option_profile: lock.option_profile.clone(),
        click_header_catalog_sha256: lock.click_header_catalog_sha256.clone(),
        unit_directory: lock.unit_directory.clone(),
        toolchain: lock.toolchain.clone(),
        sources: lock
            .sources
            .iter()
            .map(|locked| SectionSource {
                logical_source: locked.logical_source.clone(),
                path: locked.path.clone(),
                args: locked.args.clone(),
                local_dependencies: locked.local_dependencies.clone(),
                unit_dependencies: locked.unit_dependencies.clone(),
                click_headers: locked.click_headers.clone(),
            })
            .collect(),
    };
    Entry::new(
        LANGUAGE,
        lock.config_sha256.clone(),
        envelope::Frontend {
            name: "gcc".into(),
            identity: lock.invocation_sha256.clone(),
        },
        sources,
        serde_json::to_value(section).expect("a C lock section serializes"),
    )
}

/// The lock `entry` records.
fn entry_lock(entry: &Entry) -> Result<Lock, String> {
    let section = Section::deserialize(entry.section(LANGUAGE).expect("parsed for C"))
        .map_err(|error| format!("parse the C lock section: {error}"))?;
    if section.sources.len() != entry.sources.len() {
        return Err("the C lock section and the lock's sources differ".into());
    }
    let mut sources = Vec::with_capacity(section.sources.len());
    for part in section.sources {
        let recorded = entry.sources.get(&part.logical_source).ok_or_else(|| {
            format!(
                "the C lock section names a source `{}` the lock lacks",
                part.logical_source
            )
        })?;
        let mut dependencies = recorded.inputs.clone();
        let source_sha256 = dependencies
            .remove(&part.path)
            .ok_or_else(|| format!("the lock records no digest of the source `{}`", part.path))?;
        sources.push(LockedSource {
            logical_source: part.logical_source,
            path: part.path,
            args: part.args,
            artifact: recorded.artifact.path.clone(),
            source_sha256,
            artifact_sha256: recorded.artifact.sha256.clone(),
            artifact_bytes: recorded.artifact.bytes,
            dependencies,
            local_dependencies: part.local_dependencies,
            unit_dependencies: part.unit_dependencies,
            click_headers: part.click_headers,
        });
    }
    Ok(Lock {
        schema: section.schema,
        config_sha256: entry.unit.clone(),
        target: section.target,
        mode: section.mode,
        compiler_path: section.compiler_path,
        working_directory: section.working_directory,
        config_directory: section.config_directory,
        invocation_sha256: entry.frontend.identity.clone(),
        option_profile: section.option_profile,
        click_header_catalog_sha256: section.click_header_catalog_sha256,
        unit_directory: section.unit_directory,
        toolchain: section.toolchain,
        sources,
    })
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
    unit_dependencies: BTreeMap<String, String>,
    click_headers: BTreeMap<String, String>,
    source_sha256: String,
}

/// Click's system headers for one target, written to a private directory
/// for the duration of a lock refresh and removed afterwards.
#[derive(Debug)]
struct ClickHeaderDir {
    root: PathBuf,
    root_text: String,
    kinds: BTreeMap<&'static str, HeaderKind>,
    catalog_sha256: String,
}

impl Drop for ClickHeaderDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[derive(Clone, Debug)]
struct Context<'a> {
    config: &'a Config,
    click_headers: &'a ClickHeaderDir,
    invocation_sha256: String,
    toolchain: ToolchainIdentity,
    toolchain_generation: BTreeMap<String, FileState>,
    roots: Vec<PathBuf>,
    exclusions: BTreeSet<PathBuf>,
    before: SourceRootInventory,
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
struct SourceRootInventory {
    entries: BTreeMap<String, FileState>,
    bytes: u64,
}

/// A C unit of a Click project, as `click.project.json` describes it.
#[derive(Clone, Debug)]
pub(crate) struct UnitConfig {
    /// The absolute path of `click.project.json`; its directory is the
    /// project root that artifact paths are relative to.
    pub project_file: PathBuf,
    pub lock_path: PathBuf,
    pub unit_name: String,
    /// The digest of the unit's description, which its lock records.
    pub unit_digest: String,
    pub target: CTarget,
    pub optimization: COptimization,
    pub compiler: PathBuf,
    /// The unit's source root, relative to the project root.
    pub root: String,
    pub environment: BTreeMap<String, String>,
    pub option_profile: Option<String>,
    pub sources: Vec<UnitSource>,
}

#[derive(Clone, Debug)]
pub(crate) struct UnitSource {
    /// The source's path relative to the unit root; also its logical name.
    pub path: String,
    pub args: Vec<String>,
    /// The artifact's path relative to the project root.
    pub artifact: String,
    pub projection: Option<String>,
}

/// Prepares a project unit: its lock entry and the artifacts to write.
pub(crate) fn prepare_unit(
    unit: &UnitConfig,
) -> Result<(serde_json::Value, Vec<(PathBuf, Vec<u8>)>), String> {
    let config = unit_config(unit, ConfigUse::Prepare).map_err(bounded_error)?;
    let (lock, artifacts) = build_lock(&config).map_err(bounded_error)?;
    let lock = portable_lock(&config, lock)?;
    let value =
        serde_json::to_value(lock_entry(&lock)).map_err(|e| format!("encode import lock: {e}"))?;
    Ok((value, artifacts))
}

/// The lock with the project and unit roots it records replaced by their
/// labels, and the invocation digest that binds those paths recomputed over
/// the labels. Loading compares that digest only with the lock's own
/// recorded fields and resolves dependencies by stripping the recorded root,
/// so the labelled lock loads from any checkout.
fn portable_lock(config: &Config, lock: Lock) -> Result<Lock, String> {
    let project = PathBuf::from(&lock.config_directory);
    let unit = lock.unit_directory.as_ref().map(PathBuf::from);
    let mut roots = vec![("$project", project.as_path())];
    if let Some(unit) = &unit {
        roots.push(("$unit", unit.as_path()));
    }
    let labels = crate::languages::portable_paths::PathLabels::new(&roots)?;
    let text = serde_json::to_string(&lock).map_err(|e| format!("encode import lock: {e}"))?;
    let mut lock: Lock = serde_json::from_str(&labels.to_portable(&text))
        .map_err(|e| format!("encode import lock: {e}"))?;
    lock.invocation_sha256 = invocation_digest_parts(
        config.target,
        config.optimization,
        &lock.compiler_path,
        &lock.working_directory,
        &config.environment.allow,
        &lock.toolchain,
    );
    Ok(lock)
}

/// Loads a project unit's sources from its lock entry.
pub(crate) fn load_unit(
    unit: &UnitConfig,
    lock: &serde_json::Value,
) -> Result<Vec<PreparedCImport>, String> {
    let config = unit_config(unit, ConfigUse::Load).map_err(bounded_error)?;
    let entry = Entry::parse(LANGUAGE, &unit.unit_name, lock)?;
    let lock = entry_lock(&entry)?;
    let mut prepared = load_locked(&config, &lock).map_err(bounded_error)?;
    for import in &mut prepared {
        let identity = entry.checked_identity(LANGUAGE, &import.inner.logical_source)?;
        Arc::get_mut(&mut import.inner)
            .expect("a freshly loaded import is not shared")
            .identity = identity;
    }
    Ok(prepared)
}

fn unit_config(unit: &UnitConfig, use_for: ConfigUse) -> Result<Config, String> {
    let project_root = unit
        .project_file
        .parent()
        .ok_or("project file has no parent directory")?
        .to_path_buf();
    let mut config = Config {
        schema: SCHEMA,
        target: unit.target,
        optimization: unit.optimization,
        compiler: unit.compiler.clone(),
        working_directory: unit.root.clone(),
        environment: Environment {
            allow: unit.environment.clone(),
        },
        option_profile: unit.option_profile.clone(),
        sources: unit
            .sources
            .iter()
            .map(|source| SourceConfig {
                logical_source: source.path.clone(),
                path: source.path.clone(),
                args: source.args.clone(),
                artifact: source.artifact.clone(),
                projection: source.projection.clone(),
            })
            .collect(),
        config_directory: project_root,
        lock_path: unit.lock_path.clone(),
        config_path: unit.project_file.clone(),
        config_bytes_sha256: unit.unit_digest.clone(),
        origin: ConfigOrigin::ProjectUnit(unit.unit_name.clone()),
        unit_directory: None,
    };
    normalize_config(&mut config, use_for)?;
    let unit_root = fs::canonicalize(&config.working_directory).map_err(|error| {
        format!(
            "resolve the root `{}` of unit `{}`: {error}",
            unit.root, unit.unit_name
        )
    })?;
    let project_root = fs::canonicalize(&config.config_directory)
        .map_err(|error| format!("resolve project root: {error}"))?;
    if !unit_root.starts_with(&project_root) {
        config.unit_directory = Some(unit_root);
    }
    validate_config(&config, use_for)?;
    Ok(config)
}

fn load_locked(config: &Config, lock: &Lock) -> Result<Vec<PreparedCImport>, String> {
    validate_lock_shape(lock, config)?;
    if lock.option_profile != config.option_profile {
        return Err("import lock option profile does not match the import config".into());
    }
    if lock.config_sha256 != config.config_bytes_sha256 {
        return Err(match &config.origin {
            ConfigOrigin::File => "import lock does not match the import config".into(),
            ConfigOrigin::ProjectUnit(name) => format!(
                "the project lock for unit `{name}` does not match its description in `click.project.json`; run `click import lock` to prepare it again"
            ),
        });
    }
    if lock.unit_directory.is_some() != config.unit_directory.is_some() {
        return Err("import lock unit root does not match the project".into());
    }
    if lock.invocation_sha256
        != invocation_digest_parts(
            config.target,
            config.optimization,
            &lock.compiler_path,
            &lock.working_directory,
            &config.environment.allow,
            &lock.toolchain,
        )
    {
        return Err("compiler invocation identity differs from the import lock".into());
    }
    if let Some(catalog) = &lock.click_header_catalog_sha256
        && *catalog != system_headers::catalog_digest(config.c_target())
    {
        return Err(format!(
            "Click's system headers for {} changed since this import lock was prepared; run `click import lock` to prepare the import against them",
            config.target.name()
        ));
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
        validate_locked_source(source, locked, config, lock)?;
        let artifact_path = resolve_artifact(config, &source.artifact)?;
        let existing = read_stable(
            &artifact_path,
            MAX_ARTIFACT_BYTES,
            "locked artifact",
            Leaf::Follow,
        )?;
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
        let (mut clean, map) = CSourceMap::decode(text)?;
        if source.projection.is_some() {
            clean = super::projection::project_dependency_closure(&clean, &map)
                .map_err(|reason| {
                    format!(
                        "dependency-closure projection of `{}`: {reason}",
                        source.logical_source
                    )
                })?
                .text;
        }
        prepared.push(PreparedCImport {
            inner: Arc::new(PreparedInner {
                target: config.c_target(),
                logical_source: source.logical_source.clone(),
                source: clean,
                source_map: map,
                identity: String::new(),
                promises: if config.optimization.optimizes() {
                    PromiseAttributes::Refuse
                } else {
                    PromiseAttributes::Accept
                },
            }),
        });
    }
    Ok(prepared)
}

/// Runs the compiler for every source and returns the lock with the
/// artifacts it describes, without writing either.
fn build_lock(config: &Config) -> Result<(Lock, Vec<(PathBuf, Vec<u8>)>), String> {
    let click_headers = materialize_click_headers(config.c_target())?;
    let context = make_context(config, &click_headers)?;
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
            unit_dependencies: result.unit_dependencies.clone(),
            click_headers: result.click_headers.clone(),
        });
    }
    let lock = Lock {
        schema: LOCK_SCHEMA,
        config_sha256: config.config_bytes_sha256.clone(),
        target: CTarget::TRIPLE.to_string(),
        mode: config.target.mode().to_string(),
        compiler_path: config.compiler.to_string_lossy().into_owned(),
        working_directory: config.working_directory.clone(),
        config_directory: fs::canonicalize(&config.config_directory)
            .map_err(|error| format!("resolve project root: {error}"))?
            .to_string_lossy()
            .into_owned(),
        invocation_sha256: context.invocation_sha256.clone(),
        option_profile: config.option_profile.clone(),
        click_header_catalog_sha256: Some(click_headers.catalog_sha256.clone()),
        unit_directory: config
            .unit_directory
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned()),
        toolchain: context.toolchain.clone(),
        sources: locked,
    };
    let mut artifacts = Vec::with_capacity(results.len());
    for (source, result) in results {
        artifacts.push((resolve_artifact(config, &source.artifact)?, result.artifact));
    }
    Ok((lock, artifacts))
}

fn make_context<'a>(
    config: &'a Config,
    click_headers: &'a ClickHeaderDir,
) -> Result<Context<'a>, String> {
    if current_config_digest(config)? != config.config_bytes_sha256 {
        return Err("import config changed while it was being loaded".into());
    }
    let roots = canonicalize_roots(&explicit_roots(config)?)?;
    let exclusions = output_exclusions(config)?;
    let (toolchain, toolchain_generation) = discover_toolchain(config)?;
    let invocation_sha256 = invocation_digest(config, &toolchain);
    let before = inventory_roots(&roots, &exclusions)?;
    if current_config_digest(config)? != config.config_bytes_sha256 {
        return Err("import config changed while the source inventory was recorded".into());
    }
    Ok(Context {
        config,
        click_headers,
        invocation_sha256,
        toolchain,
        toolchain_generation,
        roots,
        exclusions,
        before,
    })
}

/// The digest of the configuration as it now stands on disk, to detect a
/// change during preparation.
fn current_config_digest(config: &Config) -> Result<String, String> {
    match &config.origin {
        ConfigOrigin::File => file_digest(&config.config_path),
        ConfigOrigin::ProjectUnit(name) => {
            crate::project::Project::load(&config.config_path)?.unit_digest(name)
        }
    }
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
    let mut args = fixed_args(context.config.c_target(), context.config.optimization);
    append_user_args(&mut args, source, context.config)?;
    // Click's headers take the C library's place in GCC's search order:
    // after every `-iquote`, `-I`, and `-isystem` directory the project
    // configures, so a project header found first is used, as GCC would.
    args.extend([
        "-isystem".into(),
        context.click_headers.root_text.clone(),
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
            return Err(format!(
                "preprocess {}: {}",
                source.logical_source,
                explain_compiler_diagnostic(&error, context.click_headers, context.config)
            ));
        }
    };
    let dep = read_regular(
        &dep_path,
        MAX_CONFIG_BYTES,
        "compiler dependency output",
        Leaf::Follow,
    );
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
            explain_compiler_diagnostic(
                &String::from_utf8_lossy(&output.stderr),
                context.click_headers,
                context.config
            )
        ));
    }
    let (dependencies, click_headers) = parse_dependencies(
        &dep,
        &source_path,
        &context.config.working_directory,
        &context.roots,
        &context.exclusions,
        context.click_headers,
    )?;
    let artifact = rewrite_click_header_markers(output.stdout, context.click_headers)?;
    let source_sha256 = file_digest(&source_path)?;
    let local_dependencies = local_dependencies(context.config, &dependencies)?;
    let unit_dependencies = unit_dependencies(context.config, &dependencies);
    let result = Preprocessed {
        artifact,
        dependencies,
        local_dependencies,
        unit_dependencies,
        click_headers,
        source_sha256,
    };
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

/// The dependencies under a unit root outside the project directory,
/// relative to that root.
fn unit_dependencies(
    config: &Config,
    dependencies: &BTreeMap<String, String>,
) -> BTreeMap<String, String> {
    let Some(root) = &config.unit_directory else {
        return BTreeMap::new();
    };
    dependencies
        .iter()
        .filter_map(|(path, digest)| {
            Path::new(path)
                .strip_prefix(root)
                .ok()
                .map(|relative| (relative.to_string_lossy().into_owned(), digest.clone()))
        })
        .collect()
}

fn validate_locked_source(
    source: &SourceConfig,
    locked: &LockedSource,
    config: &Config,
    lock: &Lock,
) -> Result<(), String> {
    let preparation_root = lock.config_directory.as_str();
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
    let unit_projected = match &lock.unit_directory {
        Some(root) => locked
            .dependencies
            .iter()
            .filter_map(|(path, digest)| {
                Path::new(path)
                    .strip_prefix(root)
                    .ok()
                    .map(|relative| (relative.to_string_lossy().into_owned(), digest.clone()))
            })
            .collect::<BTreeMap<_, _>>(),
        None => BTreeMap::new(),
    };
    if unit_projected != locked.unit_dependencies {
        return Err("unit dependency inventory differs from the import lock".into());
    }
    let unit_root = config.unit_directory.as_deref();
    for (base, inventory) in [
        (
            Some(config.config_directory.as_path()),
            &locked.local_dependencies,
        ),
        (unit_root, &locked.unit_dependencies),
    ] {
        for (relative, expected) in inventory {
            let Some(base) = base else {
                return Err("import lock unit root does not match the project".into());
            };
            let relative = Path::new(relative);
            if relative
                .components()
                .any(|component| !matches!(component, std::path::Component::Normal(_)))
            {
                return Err("import lock has an invalid local dependency path".into());
            }
            let path = base.join(relative);
            reject_symlink_components(&path)?;
            if file_digest(&path)? != *expected {
                return Err(format!(
                    "local dependency `{}` differs from its import lock",
                    path.display()
                ));
            }
        }
    }
    if !locked.click_headers.is_empty() {
        let current = system_headers::compiler_import_headers(config.c_target())
            .into_iter()
            .filter(|header| header.kind == HeaderKind::Modeled)
            .map(|header| (header.name, system_headers::text_digest(&header.text)))
            .collect::<BTreeMap<_, _>>();
        for (name, digest) in &locked.click_headers {
            if current.get(name.as_str()) != Some(digest) {
                return Err(format!(
                    "Click's <{name}> changed since the import lock for `{}` was prepared; run `click import lock` to prepare it again",
                    source.logical_source
                ));
            }
        }
    }
    Ok(())
}

/// The arguments every compilation for `target` at `optimization` carries.
/// An optimizing build keeps `-fno-strict-aliasing`: the strict-aliasing check
/// does not see effective types a callee or `memcpy` writes
/// (`design/effective-types.md`).
fn fixed_args(target: CTarget, optimization: COptimization) -> Vec<String> {
    let standard = match target {
        CTarget::X86_64LinuxKernel => "-std=gnu11",
        CTarget::X86_64LinuxUserspace => "-std=c11",
    };
    // Plain `char`'s signedness is fixed explicitly, so the compiler and the
    // verifier agree on it whatever the compiler's own default.
    let plain_char = match target.plain_char() {
        super::target::PlainChar::Unsigned => "-funsigned-char",
        super::target::PlainChar::Signed => "-fsigned-char",
    };
    let mut args = vec![
        standard.into(),
        "-m64".into(),
        plain_char.into(),
        "-nostdinc".into(),
    ];
    if target == CTarget::X86_64LinuxUserspace {
        args.extend(["-pthread".into(), "-D_POSIX_C_SOURCE=200809L".into()]);
    }
    args.push(optimization.flag().into());
    if optimization.optimizes() {
        args.push("-fno-strict-aliasing".into());
    }
    args
}
fn append_user_args(
    out: &mut Vec<String>,
    source: &SourceConfig,
    config: &Config,
) -> Result<(), String> {
    let args = &source.args;
    validate_source_args(source, config)?;
    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        out.push(arg.clone());
        if matches!(
            arg.as_str(),
            "-D" | "-U" | "-I" | "-iquote" | "-isystem" | "-include"
        ) {
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
    click_headers: &ClickHeaderDir,
) -> Result<(BTreeMap<String, String>, BTreeMap<String, String>), String> {
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
    let mut opened_click_headers = BTreeMap::new();
    for token in tokens {
        let path = absolute_path(Path::new(&token), Path::new(cwd))?;
        let canonical = fs::canonicalize(&path)
            .map_err(|e| format!("canonicalize compiler dependency {}: {e}", path.display()))?;
        if canonical == canonical_source {
            continue;
        }
        if let Ok(relative) = canonical.strip_prefix(&click_headers.root) {
            let name = relative.to_string_lossy();
            let Some((&name, HeaderKind::Modeled)) = click_headers.kinds.get_key_value(&*name)
            else {
                return Err(format!(
                    "compiler opened `{name}` from Click's system headers, which is not a modeled header"
                ));
            };
            opened_click_headers.insert(name.to_string(), file_digest(&canonical)?);
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
    Ok((result, opened_click_headers))
}

/// Writes Click's system headers for `target` to a fresh private directory.
fn materialize_click_headers(target: CTarget) -> Result<ClickHeaderDir, String> {
    static NEXT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| format!("clock: {e}"))?
        .as_nanos();
    let created = std::env::temp_dir().join(format!(
        "click-import-headers-{}-{nanos}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    fs::create_dir(&created).map_err(|e| format!("create Click's system header directory: {e}"))?;
    let root = match fs::canonicalize(&created) {
        Ok(root) => root,
        Err(error) => {
            let _ = fs::remove_dir_all(&created);
            return Err(format!("resolve Click's system header directory: {error}"));
        }
    };
    let root_text = root.to_string_lossy().into_owned();
    let mut dir = ClickHeaderDir {
        root,
        root_text,
        kinds: BTreeMap::new(),
        catalog_sha256: system_headers::catalog_digest(target),
    };
    // Line markers name these files; a plain path is spelled the same in
    // every marker, so it can be replaced exactly.
    if !dir
        .root_text
        .bytes()
        .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'/' | b'.' | b'_' | b'-'))
    {
        return Err(format!(
            "temporary directory `{}` must be a plain path to hold Click's system headers",
            dir.root_text
        ));
    }
    for header in system_headers::compiler_import_headers(target) {
        let path = dir.root.join(header.name);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| format!("write Click's system headers: {e}"))?;
        }
        fs::write(&path, header.text.as_bytes())
            .map_err(|e| format!("write Click's system headers: {e}"))?;
        dir.kinds.insert(header.name, header.kind);
    }
    Ok(dir)
}

/// Renames Click's header files in the artifact's line markers from their
/// temporary path to `<header>`, so the artifact does not depend on where the
/// headers were written.
fn rewrite_click_header_markers(
    artifact: Vec<u8>,
    headers: &ClickHeaderDir,
) -> Result<Vec<u8>, String> {
    let needle = format!("\"{}/", headers.root_text);
    let Ok(text) = std::str::from_utf8(&artifact) else {
        if artifact
            .windows(headers.root_text.len())
            .any(|window| window == headers.root_text.as_bytes())
        {
            return Err("compiler output that names Click's system headers is not UTF-8".into());
        }
        return Ok(artifact);
    };
    if !text.contains(headers.root_text.as_str()) {
        return Ok(artifact);
    }
    let mut output = String::with_capacity(text.len());
    for line in text.split_inclusive('\n') {
        let marker =
            line.starts_with("# ") && line[2..].bytes().next().is_some_and(|b| b.is_ascii_digit());
        if let Some(start) = line.find(&needle).filter(|_| marker) {
            let after = &line[start + needle.len()..];
            let end = after
                .find('"')
                .ok_or("unterminated line marker naming Click's system headers")?;
            let name = &after[..end];
            if headers.kinds.get(name) != Some(&HeaderKind::Modeled) {
                return Err(format!(
                    "compiler output names `{name}` from Click's system headers, which is not a modeled header"
                ));
            }
            output.push_str(&line[..start]);
            output.push_str(&format!("\"<{name}>\""));
            output.push_str(&after[end + 1..]);
        } else {
            output.push_str(line);
        }
    }
    if output.contains(headers.root_text.as_str()) {
        return Err(
            "compiler output names Click's temporary system header directory outside a line marker"
                .into(),
        );
    }
    Ok(output.into_bytes())
}

/// A compiler diagnostic with Click's temporary header directory named as
/// `<click>`, and, for a missing header, which system headers Click supplies.
fn explain_compiler_diagnostic(
    diagnostic: &str,
    headers: &ClickHeaderDir,
    config: &Config,
) -> String {
    let mut message = diagnostic.replace(&format!("{}/", headers.root_text), "<click>/");
    if message.contains("No such file or directory") {
        let target = config.c_target();
        message.push_str(&format!(
            "\nnote: the system headers Click supplies for {} are <{}>; see {}. Project headers are found through -iquote, -I, and -isystem directories",
            target.name(),
            system_headers::modeled_header_names(target)
                .iter()
                .filter(|name| headers.kinds.get(*name) == Some(&HeaderKind::Modeled))
                .copied()
                .collect::<Vec<_>>()
                .join(">, <"),
            system_headers::COVERAGE_REFERENCE
        ));
    }
    message
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
    if let Some(name) = &config.option_profile {
        OptionProfile::named(name, config.c_target())?;
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
        validate_source_args(source, config)?;
        if let Some(projection) = &source.projection
            && projection != super::projection::DEPENDENCY_CLOSURE
        {
            return Err(format!(
                "unsupported import projection `{projection}`; only `{}` is supported",
                super::projection::DEPENDENCY_CLOSURE
            ));
        }
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

fn validate_source_args(source: &SourceConfig, config: &Config) -> Result<(), String> {
    validate_args(
        &source.args,
        config.c_target(),
        config.optimization,
        config.profile(),
    )
    .map_err(|error| format!("source `{}`: {error}", source.logical_source))
}

fn validate_args(
    args: &[String],
    target: CTarget,
    optimization: COptimization,
    profile: Option<&OptionProfile>,
) -> Result<(), String> {
    if args.len() > MAX_ARGUMENTS
        || args.iter().map(String::len).sum::<usize>() > MAX_ARGUMENT_BYTES
    {
        return Err("compiler argument list exceeds bounds".into());
    }
    let profile_args = fixed_args(target, optimization);
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
            return Err(format!("unsupported compiler argument {} `{arg}`", i + 1));
        }
        if profile_args.contains(arg) || profile.is_some_and(|profile| profile.accepts(arg)) {
            i += 1;
            continue;
        }
        if arg.starts_with("-O") {
            return Err(format!(
                "compiler argument {} `{arg}` names an optimization level; the project verifies \
                 its units at `{}`, set by `optimization` in `click.project.json`",
                i + 1,
                optimization.flag()
            ));
        }
        let separate = matches!(
            arg.as_str(),
            "-D" | "-U" | "-I" | "-iquote" | "-isystem" | "-include"
        );
        let prefix = arg.starts_with("-D")
            || arg.starts_with("-U")
            || arg.starts_with("-I")
            || arg.starts_with("-iquote")
            || arg.starts_with("-isystem")
            || arg.starts_with("-include");
        if !prefix {
            return Err(match profile {
                None => format!(
                    "unsupported compiler argument {} `{arg}`; only -D/-U/-I/-iquote/-isystem/-include are supported",
                    i + 1
                ),
                Some(profile) => format!(
                    "unsupported compiler argument {} `{arg}`; option profile `{}` accepts only its listed spellings beside -D/-U/-I/-iquote/-isystem/-include",
                    i + 1,
                    profile.name
                ),
            });
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
    if let Some(profile) = profile {
        profile.check_vector(args)?;
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
    if matches!(name, "__OPTIMIZE__" | "__NO_INLINE__") {
        return Err(format!(
            "cannot override optimization macro {name}; set `optimization` in `click.project.json`"
        ));
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
            let (kind, value) =
                if matches!(arg.as_str(), "-I" | "-iquote" | "-isystem" | "-include") {
                    i += 1;
                    if i == source.args.len() {
                        return Err(format!("missing value after {arg}"));
                    }
                    (arg.as_str(), source.args[i].as_str())
                } else if let Some(v) = arg.strip_prefix("-isystem") {
                    ("-isystem", v)
                } else if let Some(v) = arg.strip_prefix("-iquote") {
                    ("-iquote", v)
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

fn inventory_roots(
    roots: &[PathBuf],
    exclusions: &BTreeSet<PathBuf>,
) -> Result<SourceRootInventory, String> {
    let mut entries = BTreeMap::new();
    let mut bytes = 0;
    let mut roots = roots.to_vec();
    roots.sort();
    let selected = prune_roots(roots);
    for root in selected {
        program_point_path(&root, exclusions, &mut entries, &mut bytes, 0)?;
    }
    Ok(SourceRootInventory { entries, bytes })
}

fn program_point_path(
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
            program_point_path(&child.path(), exclusions, entries, bytes, depth + 1)?;
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
    let after = inventory_roots(&context.roots, &context.exclusions)?;
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
        for (path, state) in inventory_roots(&[include], &BTreeSet::new())?.entries {
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
    write_file_atomically(&path, b"int click_import_abi_probe;\n")?;
    let mut args = fixed_args(config.c_target(), config.optimization);
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
    // Plain `char` is unsigned exactly when the compiler defines
    // `__CHAR_UNSIGNED__`; the probe checks it matches the target's.
    let char_unsigned = macros
        .lines()
        .any(|line| line.trim() == "#define __CHAR_UNSIGNED__ 1");
    if char_unsigned != (config.c_target().plain_char() == super::target::PlainChar::Unsigned) {
        return Err(format!(
            "compiler ABI probe found plain `char` {}, but target `{}` gives it {}",
            if char_unsigned { "unsigned" } else { "signed" },
            config.c_target().name(),
            if char_unsigned { "signed" } else { "unsigned" },
        ));
    }
    for expected in [
        "#define __x86_64__ 1",
        "#define __LP64__ 1",
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

fn lock_path_from_config(config: &Config) -> PathBuf {
    config.lock_path.clone()
}
fn resolve_source(config: &Config, path: &str) -> Result<PathBuf, String> {
    absolute_path(Path::new(path), Path::new(&config.working_directory))
}
fn resolve_artifact(config: &Config, path: &str) -> Result<PathBuf, String> {
    absolute_path(Path::new(path), &config.config_directory)
}
// Root aliases could change while their canonical target state stayed
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
        config.target,
        config.optimization,
        &config.compiler.to_string_lossy(),
        &config.working_directory,
        &config.environment.allow,
        toolchain,
    )
}

fn invocation_digest_parts(
    target: CTarget,
    optimization: COptimization,
    compiler_path: &str,
    working_directory: &str,
    environment: &BTreeMap<String, String>,
    toolchain: &ToolchainIdentity,
) -> String {
    let mut bytes = serde_json::to_vec(&(
        target.name(),
        compiler_path,
        working_directory,
        environment,
        toolchain,
    ))
    .expect("identity serializes");
    bytes.extend_from_slice(fixed_args(target, optimization).join("\0").as_bytes());
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
fn validate_lock_shape(lock: &Lock, config: &Config) -> Result<(), String> {
    if lock.target != CTarget::TRIPLE || lock.mode != config.target.mode() {
        return Err(format!(
            "the import lock was not prepared for target {}; run `click import lock` to prepare it again",
            config.target.name()
        ));
    }
    if lock.schema != LOCK_SCHEMA || lock.click_header_catalog_sha256.is_none() {
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
fn file_digest(path: &Path) -> Result<String, String> {
    let mut file = open_regular(path, "input", Leaf::Follow)?;
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    /// A project unit whose root is an external tree beside the project,
    /// locked by hand as the offline fixture is: its files are rechecked
    /// relative to the unit root, and the sidecar names the source by its own
    /// relative path.
    #[test]
    fn project_unit_loads_an_external_root_offline() {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = fs::canonicalize(std::env::temp_dir())
            .unwrap()
            .join(format!(
                "click-c-unit-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
        let upstream = root.join("upstream");
        let proofs = root.join("proofs");
        fs::create_dir_all(&upstream).unwrap();
        fs::create_dir_all(proofs.join("checks")).unwrap();
        fs::create_dir_all(proofs.join(".click/up")).unwrap();
        let source = b"#include \"local.h\"\nint answer(void) { return VALUE; }\n";
        let header = b"#define VALUE 42\n";
        let artifact = b"int answer(void) { return 42; }\n";
        fs::write(upstream.join("main.c"), source).unwrap();
        fs::write(upstream.join("local.h"), header).unwrap();
        fs::write(proofs.join(".click/up/main.c.i"), artifact).unwrap();
        let sidecar = proofs.join("checks/main.click");
        let proof = "target \"x86_64-unknown-linux-gnu\"; mode \"kernel\"; verifying \"../../upstream/main.c\"; int answer() { ensures result == 42; }";
        fs::write(&sidecar, proof).unwrap();
        let describe = |args: &[&str]| {
            serde_json::json!({
                "target": "x86_64-unknown-linux-gnu",
                "mode": "kernel",
                "units": {"up": {
                    "language": "c",
                    "root": "../upstream",
                    "compiler": "/toolchain/not-installed/gcc",
                    "args": args,
                    "sources": {"main.c": {}}
                }}
            })
            .to_string()
        };
        let project_file = proofs.join(crate::project::FILE_NAME);
        fs::write(&project_file, describe(&[])).unwrap();
        let project = crate::project::Project::load(&project_file).unwrap();
        let config = unit_config(&project.c_unit("up").unwrap(), ConfigUse::Load).unwrap();
        let unit_directory = config
            .unit_directory
            .clone()
            .expect("an external unit root");
        assert_eq!(unit_directory, upstream);
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
        let invocation_sha256 = invocation_digest_parts(
            config.target,
            config.optimization,
            &compiler_path,
            &config.working_directory,
            &config.environment.allow,
            &toolchain,
        );
        let catalog = system_headers::catalog_digest(CTarget::X86_64LinuxKernel);
        let dependencies = BTreeMap::from([(
            upstream.join("local.h").to_string_lossy().into_owned(),
            hex_digest(header),
        )]);
        let unit_dependencies = BTreeMap::from([("local.h".to_string(), hex_digest(header))]);
        let source_config = &config.sources[0];
        let locked = LockedSource {
            logical_source: source_config.logical_source.clone(),
            path: source_config.path.clone(),
            args: source_config.args.clone(),
            artifact: source_config.artifact.clone(),
            source_sha256: hex_digest(source),
            artifact_sha256: hex_digest(artifact),
            artifact_bytes: artifact.len(),
            dependencies: dependencies.clone(),
            local_dependencies: BTreeMap::new(),
            unit_dependencies,
            click_headers: BTreeMap::new(),
        };
        let lock = Lock {
            schema: LOCK_SCHEMA,
            config_sha256: config.config_bytes_sha256.clone(),
            target: CTarget::TRIPLE.to_string(),
            mode: config.target.mode().to_string(),
            compiler_path,
            working_directory: config.working_directory.clone(),
            config_directory: proofs.to_string_lossy().into_owned(),
            invocation_sha256,
            option_profile: None,
            click_header_catalog_sha256: Some(catalog),
            unit_directory: Some(upstream.to_string_lossy().into_owned()),
            toolchain,
            sources: vec![locked],
        };
        fs::write(
            proofs.join(crate::project::LOCK_NAME),
            serde_json::to_vec(&serde_json::json!({
                "schema": 1,
                "units": {"up": {"language": "c", "lock": lock_entry(&lock)}}
            }))
            .unwrap(),
        )
        .unwrap();

        let load = || match crate::cli::read_verification_inputs(&sidecar, proof)? {
            crate::cli::VerificationInput::Prepared(imports) => Ok(imports),
            _ => Err("expected the unit's prepared source".to_string()),
        };
        let imports = load().unwrap();
        assert_eq!(imports[0].logical_source(), "../../upstream/main.c");
        assert_eq!(imports[0].source(), "int answer(void) { return 42; }\n");
        crate::surface::verify_c_prepared_sources(proof, &imports).unwrap();

        fs::write(upstream.join("local.h"), "#define VALUE 43\n").unwrap();
        let error = load().unwrap_err();
        assert!(
            error.contains("local.h") && error.contains("differs from its import lock"),
            "{error}"
        );
        fs::write(upstream.join("local.h"), header).unwrap();
        load().unwrap();

        // A changed source or artifact cannot reuse the lock.
        for (path, original, replacement) in [
            (
                upstream.join("main.c"),
                &source[..],
                &b"int answer(void) { return 43; }\n"[..],
            ),
            (
                proofs.join(".click/up/main.c.i"),
                &artifact[..],
                &b"int answer(void) { return 43; }\n"[..],
            ),
        ] {
            fs::write(&path, replacement).unwrap();
            assert!(load().is_err(), "{}", path.display());
            fs::write(&path, original).unwrap();
        }
        load().unwrap();

        // Neither can a lock whose recorded toolchain, unit dependencies or
        // option profile differ from what was prepared.
        let lock_file = proofs.join(crate::project::LOCK_NAME);
        let original_lock = fs::read(&lock_file).unwrap();
        for field in ["toolchain", "unit_dependencies", "option_profile"] {
            let mut altered: serde_json::Value = serde_json::from_slice(&original_lock).unwrap();
            let entry = &mut altered["units"]["up"]["lock"];
            match field {
                "toolchain" => {
                    entry["c"]["toolchain"]["driver_sha256"] =
                        serde_json::json!(hex_digest(b"other"))
                }
                "option_profile" => {
                    entry["c"]["option_profile"] = serde_json::json!("linux-6.8-x86_64-kbuild")
                }
                _ => entry["c"]["sources"][0]["unit_dependencies"] = serde_json::json!({}),
            }
            fs::write(&lock_file, serde_json::to_vec(&altered).unwrap()).unwrap();
            let error = load().expect_err(field);
            if field == "option_profile" {
                assert!(error.contains("option profile does not match"), "{error}");
            }
        }
        // An entry in the shape before the shared envelope is refused with
        // the command that prepares it again.
        let mut altered: serde_json::Value = serde_json::from_slice(&original_lock).unwrap();
        altered["units"]["up"]["lock"] = serde_json::to_value(&lock).unwrap();
        fs::write(&lock_file, serde_json::to_vec(&altered).unwrap()).unwrap();
        let error = load().unwrap_err();
        assert!(
            error.contains("is in an earlier format; run `click import lock`"),
            "{error}"
        );
        fs::write(&lock_file, original_lock).unwrap();
        load().unwrap();

        fs::write(&project_file, describe(&["-DVALUE=42"])).unwrap();
        let error = load().unwrap_err();
        assert!(error.contains("does not match its description"), "{error}");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn linux_gcc_import_verifies_offline_after_relocation() {
        struct CopiedFixture(PathBuf);
        impl Drop for CopiedFixture {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }

        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let original =
            Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/cross-host-c-import");
        let root = fs::canonicalize(std::env::temp_dir())
            .unwrap()
            .join(format!(
                "click-c-real-offline-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
        fs::create_dir(&root).unwrap();
        let fixture = CopiedFixture(root);
        for name in [
            "main.c",
            "bits.h",
            "local.h",
            "main.click",
            crate::project::FILE_NAME,
            crate::project::LOCK_NAME,
            ".click/main/main.c.i",
        ] {
            let destination = fixture.0.join(name);
            fs::create_dir_all(destination.parent().unwrap()).unwrap();
            fs::copy(original.join(name), destination).unwrap();
        }
        let project_lock: serde_json::Value =
            serde_json::from_slice(&fs::read(fixture.0.join(crate::project::LOCK_NAME)).unwrap())
                .unwrap();
        let lock = entry_lock(
            &Entry::parse(LANGUAGE, "main", &project_lock["units"]["main"]["lock"]).unwrap(),
        )
        .unwrap();
        assert_ne!(lock.config_directory, fixture.0.to_string_lossy());
        // The program's own headers are its only dependencies: a standard
        // interface such as `<limits.h>` comes from Click, not the platform.
        assert_eq!(
            lock.sources[0]
                .local_dependencies
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            ["bits.h", "local.h"]
        );
        assert_eq!(
            lock.sources[0].dependencies.len(),
            lock.sources[0].local_dependencies.len()
        );
        #[cfg(target_os = "macos")]
        assert!(
            !Path::new(&lock.toolchain.cc1_path).exists(),
            "the Linux compiler backend must be absent on the Mac verification host"
        );

        let sidecar = fixture.0.join("main.click");
        let proof = fs::read_to_string(&sidecar).unwrap();
        let crate::cli::VerificationInput::Prepared(imports) =
            crate::cli::read_verification_inputs(&sidecar, &proof).unwrap()
        else {
            panic!("ordinary loading must select the locked GCC artifact");
        };
        let original_sidecar = original.join("main.click");
        let crate::cli::VerificationInput::Prepared(original_imports) =
            crate::cli::read_verification_inputs(&original_sidecar, &proof).unwrap()
        else {
            panic!("the committed fixture must select its locked GCC artifact");
        };
        assert_eq!(imports[0].identity(), original_imports[0].identity());
        assert!(imports[0].source().contains("return 8"));
        assert!(imports[0].source().contains("+ 34;"));
        let verified = crate::surface::verify_c_prepared_sources(&proof, &imports).unwrap();
        assert_eq!(
            verified[0].import_identity.as_deref(),
            Some(imports[0].identity())
        );
        let offset = proof.find("ensures").unwrap();
        let line = proof[..offset]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        let column = offset - proof[..offset].rfind('\n').unwrap();
        let expanded =
            crate::surface::expand_c_prepared_tactic_source_at(&proof, &imports, line, column)
                .unwrap();
        assert_ne!(expanded, proof);
        crate::surface::verify_c_prepared_sources(&expanded, &imports).unwrap();

        let header = fixture.0.join("local.h");
        fs::write(&header, "#define LOCAL_OFFSET 35\n").unwrap();
        assert!(crate::cli::read_verification_inputs(&sidecar, &proof).is_err());
        fs::copy(original.join("local.h"), &header).unwrap();
        let artifact = fixture.0.join(".click/main/main.c.i");
        fs::write(&artifact, "int answer(void) { return 43; }\n").unwrap();
        assert!(crate::cli::read_verification_inputs(&sidecar, &proof).is_err());
    }

    #[test]
    fn rejects_ambient_or_executable_compiler_options() {
        assert!(
            validate_args(
                &["-fplugin=evil.so".into()],
                CTarget::SUPPORTED,
                COptimization::O2,
                None
            )
            .is_err()
        );
        assert!(
            validate_args(&["-c".into()], CTarget::SUPPORTED, COptimization::O2, None).is_err()
        );
        assert!(
            validate_args(
                &["@args.rsp".into()],
                CTarget::SUPPORTED,
                COptimization::O2,
                None
            )
            .is_err()
        );
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
                "-iquote".into(),
                "quoted".into(),
                "-iquotequoted".into(),
                "-isystem".into(),
                "/usr/include".into(),
                "-include".into(),
                "config.h".into(),
            ],
            CTarget::X86_64LinuxKernel,
            COptimization::O2,
            None,
        )
        .unwrap();
    }

    fn args(spellings: &[&str]) -> Vec<String> {
        spellings
            .iter()
            .map(|spelling| spelling.to_string())
            .collect()
    }

    fn kbuild() -> Option<&'static OptionProfile> {
        Some(&super::super::option_profile::LINUX_KBUILD)
    }

    #[test]
    fn kbuild_profile_accepts_each_listed_spelling_only_when_selected() {
        let profile = kbuild().unwrap();
        validate_args(
            &args(profile.accepted()),
            CTarget::X86_64LinuxKernel,
            COptimization::O2,
            kbuild(),
        )
        .unwrap();
        for spelling in profile.accepted() {
            // `-mno-sse` and `-mno-sse2` need the x87 disabled.
            let mut vector = args(&[spelling]);
            vector.extend(args(&profile.requirements(spelling)));
            validate_args(
                &vector,
                CTarget::X86_64LinuxKernel,
                COptimization::O2,
                kbuild(),
            )
            .unwrap_or_else(|error| panic!("{spelling}: {error}"));
            let error = validate_args(&vector, CTarget::X86_64LinuxKernel, COptimization::O2, None)
                .expect_err("profile options need the profile");
            assert!(
                error.contains(&format!("argument 1 `{spelling}`"))
                    && error.contains("only -D/-U/-I/-iquote/-isystem/-include"),
                "{spelling}: {error}"
            );
        }
    }

    #[test]
    fn kbuild_profile_refuses_near_misses_with_a_located_message() {
        // For each accepted family, a different value and an unlisted
        // sibling. Several of these are themselves harmless; the profile is
        // closed, so they are refused until classified.
        for near_miss in [
            // Preprocessing.
            "-fmacro-prefix-map=/=",
            "-ffile-prefix-map=./=",
            "-fdebug-prefix-map=./=",
            // Diagnostics, and the `-W` spellings that pass options on.
            "-Wframe-larger-than=1",
            "-Wimplicit-fallthrough=3",
            "-Werror=vla",
            "-Wno-vla",
            "-Wextra",
            "-Wp,-DX=1",
            "-Wa,--noexecstack",
            "-Wl,-z,now",
            // Source semantics.
            "-fcommon",
            "-fdelete-null-pointer-checks",
            "-fstrict-aliasing",
            "-fstrict-overflow",
            "-fwrapv",
            "-fsigned-char",
            "-fno-short-wchar",
            "-fshort-enums",
            "-fpack-struct",
            "-fstrict-flex-arrays=2",
            "-fstrict-flex-arrays",
            "-ftrivial-auto-var-init=pattern",
            "-ftrivial-auto-var-init=uninitialized",
            "-fallow-store-data-races",
            "-ffast-math",
            // Code generation.
            "-falign-functions=32",
            "-falign-labels=1",
            "-fpatchable-function-entry=16,0",
            "-fcf-protection=full",
            "-fstack-protector-all",
            "-fPIE",
            "-fno-omit-frame-pointer",
            // Target.
            "-mcmodel=large",
            "-mindirect-branch=thunk",
            "-mfunction-return=keep",
            "-mpreferred-stack-boundary=4",
            "-mtune=native",
            "-march=native",
            "-mno-sse3",
            "-msse",
            "-m80387",
            "-m32",
            "-mabi=ms",
            // Optimization levels.
            "-O0",
            "-O3",
            "-Os",
            "-O",
            // Fixed by the target, with another value.
            "-std=gnu17",
            "-std=c11",
        ] {
            let error = validate_args(
                &args(&["-mno-80387", near_miss]),
                CTarget::X86_64LinuxKernel,
                COptimization::O2,
                kbuild(),
            )
            .expect_err(near_miss);
            assert!(
                error.contains(&format!("argument 2 `{near_miss}`")),
                "{near_miss}: {error}"
            );
        }
    }

    #[test]
    fn a_unit_names_only_the_projects_optimization_level() {
        // The project's level is a fixed argument; a unit may repeat it, as
        // the recorded Kbuild command line does, without the safety options
        // GCC no longer needs once Click checks what they guarded.
        for profile in [None, kbuild()] {
            validate_args(
                &args(&["-O2"]),
                CTarget::X86_64LinuxKernel,
                COptimization::O2,
                profile,
            )
            .unwrap();
        }
        for (level, other) in [(COptimization::O2, "-O0"), (COptimization::O0, "-O2")] {
            let error = validate_args(&args(&[other]), CTarget::X86_64LinuxKernel, level, kbuild())
                .unwrap_err();
            assert!(
                error.contains(&format!(
                    "argument 1 `{other}` names an optimization level; the project verifies its units at `{}`",
                    level.flag()
                )),
                "{error}"
            );
        }
        let error = validate_args(
            &args(&["-D__OPTIMIZE__"]),
            CTarget::X86_64LinuxUserspace,
            COptimization::O0,
            None,
        )
        .unwrap_err();
        assert!(
            error.contains("cannot override optimization macro __OPTIMIZE__"),
            "{error}"
        );
    }

    #[test]
    fn an_optimizing_build_keeps_strict_aliasing_off_until_the_check_is_complete() {
        let optimized = fixed_args(CTarget::X86_64LinuxUserspace, COptimization::O2);
        assert!(optimized.iter().any(|arg| arg == "-O2"));
        assert!(optimized.iter().any(|arg| arg == "-fno-strict-aliasing"));
        let unoptimized = fixed_args(CTarget::X86_64LinuxUserspace, COptimization::O0);
        assert!(unoptimized.iter().any(|arg| arg == "-O0"));
        assert!(!unoptimized.iter().any(|arg| arg == "-fno-strict-aliasing"));
    }

    #[test]
    fn kbuild_profile_disables_sse_only_beside_the_x87() {
        for option in ["-mno-sse", "-mno-sse2"] {
            let error = validate_args(
                &args(&["-Wall", option]),
                CTarget::X86_64LinuxKernel,
                COptimization::O2,
                kbuild(),
            )
            .unwrap_err();
            assert!(
                error.contains(&format!("argument 2 `{option}` needs `-mno-80387`"))
                    && error.contains("excess precision"),
                "{error}"
            );
            validate_args(
                &args(&["-mno-80387", option]),
                CTarget::X86_64LinuxKernel,
                COptimization::O2,
                kbuild(),
            )
            .unwrap();
        }
    }

    #[test]
    fn option_profiles_are_named_and_target_bound() {
        assert!(
            OptionProfile::named("linux-6.8-x86_64-kbuild", CTarget::X86_64LinuxKernel).is_ok()
        );
        let unknown = OptionProfile::named("linux-6.9-x86_64-kbuild", CTarget::X86_64LinuxKernel)
            .unwrap_err();
        assert!(
            unknown.contains("unknown compiler option profile"),
            "{unknown}"
        );
        let wrong_target =
            OptionProfile::named("linux-6.8-x86_64-kbuild", CTarget::X86_64LinuxUserspace)
                .unwrap_err();
        assert!(
            wrong_target.contains("applies only to target"),
            "{wrong_target}"
        );
    }

    /// Every recorded rbtree option is classified and accepted under the
    /// profile.
    #[test]
    fn linux_rbtree_vector_is_classified_by_the_kbuild_profile() {
        let project: serde_json::Value = serde_json::from_slice(
            &fs::read(
                Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("integrations/linux-rbtree/click.project.json"),
            )
            .unwrap(),
        )
        .unwrap();
        let config = &project["units"]["linux"];
        assert_eq!(config["option_profile"], "linux-6.8-x86_64-kbuild");
        let vector = config["args"]
            .as_array()
            .unwrap()
            .iter()
            .map(|argument| argument.as_str().unwrap().to_string())
            .collect::<Vec<_>>();
        validate_args(
            &vector,
            CTarget::X86_64LinuxKernel,
            COptimization::O2,
            kbuild(),
        )
        .unwrap();
    }

    /// The classification table in the `click import` reference lists exactly
    /// the profile's accepted spellings, and for each the options it needs.
    #[test]
    fn kbuild_profile_matches_its_documented_classification() {
        let docs = fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("docs/reference/cli/import.md"),
        )
        .unwrap();
        let heading = "### Option profile `linux-6.8-x86_64-kbuild`";
        let section = docs
            .split_once(heading)
            .unwrap_or_else(|| panic!("missing `{heading}`"))
            .1;
        let section = section.split("\n#").next().unwrap();
        let profile = kbuild().unwrap();
        let mut accepted = BTreeSet::new();
        for row in section.lines().filter(|line| line.starts_with("| `")) {
            let cells = row.split(" | ").collect::<Vec<_>>();
            let spelling = cells[0]
                .trim_start_matches("| `")
                .split('`')
                .next()
                .unwrap()
                .to_string();
            match cells[1] {
                "Accepted" => assert!(profile.requirements(&spelling).is_empty(), "{row}"),
                verdict if verdict.starts_with("Accepted with ") => {
                    let documented = verdict["Accepted with ".len()..]
                        .split(", ")
                        .map(|required| required.trim_matches('`'))
                        .collect::<Vec<_>>();
                    assert_eq!(documented, profile.requirements(&spelling), "{row}");
                }
                "Base" | "Fixed" => continue,
                verdict => panic!("unknown verdict `{verdict}` in {row}"),
            }
            assert!(accepted.insert(spelling), "{row}");
        }
        assert_eq!(
            accepted,
            profile.accepted().iter().map(|s| s.to_string()).collect()
        );
    }

    #[test]
    fn dependency_lexer_preserves_escaped_spaces() {
        assert_eq!(
            dep_tokens("x.o: a\\ b.h c\\#d.h\\\n next.h\n").unwrap(),
            vec!["x.o", "a b.h", "c#d.h", "next.h"]
        );
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
                &BTreeSet::new(),
                &materialize_click_headers(CTarget::X86_64LinuxKernel).unwrap()
            )
            .is_err()
        );
        let _ = fs::remove_dir_all(&root);
        let _ = fs::remove_file(&outside);
    }

    // macOS `/usr/bin/gcc` is Apple Clang and has no GNU `cc1` executable.
    #[cfg(not(target_os = "macos"))]
    #[test]
    #[ignore = "nightly: 3s in the parallel gate"]
    fn real_gcc_round_trip_uses_fixed_c_profile() {
        let root = std::env::temp_dir().join(format!("click-import-test-{}", std::process::id()));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        fs::write(
            root.join("x.c"),
            b"#define VALUE 7\nint imported = VALUE;\nconst char *source_file = __FILE__;\n",
        )
        .unwrap();
        let project_file = root.join(crate::project::FILE_NAME);
        fs::write(
            &project_file,
            serde_json::json!({"target": "x86_64-unknown-linux-gnu", "mode": "kernel", "units": {"x": {
                "language": "c",
                "compiler": "/usr/bin/gcc",
                "env": {"PATH": std::env::var("PATH").unwrap_or_default()},
                "sources": {"x.c": {}}
            }}})
            .to_string(),
        )
        .unwrap();
        let project = crate::project::Project::load(&project_file).unwrap();
        project.lock().unwrap();
        let Some(crate::project::UnitSelection::C(imports)) = project
            .prepared_sources(&[("x.c".into(), fs::canonicalize(root.join("x.c")).ok())])
            .unwrap()
        else {
            panic!("the unit prepares its C source");
        };
        assert!(imports[0].source().contains("imported = 7"));
        assert!(imports[0].source().contains("source_file = \"x.c\""));
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn malformed_inputs_and_diagnostics_remain_bounded() {
        assert!(bounded_error("é".repeat(20000)).len() <= 16 * 1024);
        assert_eq!(
            dep_tokens("x.o: dollar$$.h\n").unwrap(),
            vec!["x.o", "dollar$.h"]
        );
    }

    #[cfg(unix)]
    #[test]
    fn nonregular_inputs_and_cancelled_states_fail_promptly() {
        use std::os::unix::ffi::OsStrExt;
        let path = std::env::temp_dir().join(format!("click-import-fifo-{}", std::process::id()));
        let _cleanup = RemoveFile(path.clone());
        let name = std::ffi::CString::new(path.as_os_str().as_bytes()).unwrap();
        assert_eq!(unsafe { libc::mkfifo(name.as_ptr(), 0o600) }, 0);
        assert!(
            read_regular(&path, 64, "config", Leaf::Follow)
                .unwrap_err()
                .contains("regular")
        );
        assert!(file_digest(&path).unwrap_err().contains("regular"));
        let cancelled = crate::instrumentation::with_deadline(Duration::ZERO, || {
            inventory_roots(&[path], &BTreeSet::new())
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
            let compact = inventory_roots(std::slice::from_ref(&input), &BTreeSet::new()).unwrap();
            let overlapping = inventory_roots(&roots, &BTreeSet::new()).unwrap();
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
}
