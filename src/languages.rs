//! Program languages supported by Surface Click.

use std::fs;
use std::path::Path;

pub mod c;
pub(crate) mod compiler_process;
pub mod cpp;
pub mod rust;

/// The language a program's sources are written in.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SourceLanguage {
    C,
    Cpp,
    Rust,
}

impl SourceLanguage {
    /// The language of the source a `verifying` clause names, by its
    /// extension.
    pub fn of_source_path(path: &str) -> Self {
        if path.ends_with(".rs") {
            Self::Rust
        } else if path.ends_with(".cpp") {
            Self::Cpp
        } else {
            Self::C
        }
    }

    /// The language of a file's `verifying` sources: Rust when any is a Rust
    /// source, since that decides which signature syntax the sidecar admits.
    pub fn of_sources<'p>(paths: impl IntoIterator<Item = &'p str>) -> Self {
        paths
            .into_iter()
            .map(Self::of_source_path)
            .max_by_key(|language| *language == Self::Rust)
            .unwrap_or(Self::C)
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::C => "C",
            Self::Cpp => "C++",
            Self::Rust => "Rust",
        }
    }
}

impl std::fmt::Display for SourceLanguage {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.name())
    }
}

#[derive(Clone, Debug)]
pub enum PreparedCompilerImport {
    C(Vec<c::compiler_import::PreparedCImport>),
    Program(PreparedProgram),
}

fn import_language(config_path: &Path) -> Result<Option<String>, String> {
    const MAX_CONFIG_BYTES: u64 = 1 << 20;
    let metadata = fs::symlink_metadata(config_path)
        .map_err(|error| format!("read import config `{}`: {error}", config_path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > MAX_CONFIG_BYTES {
        return Err("compiler import config must be a regular file of at most 1 MiB".into());
    }
    let bytes = fs::read(config_path)
        .map_err(|error| format!("read import config `{}`: {error}", config_path.display()))?;
    if bytes.len() > MAX_CONFIG_BYTES as usize {
        return Err("compiler import config exceeds its 1 MiB limit".into());
    }
    let value: serde_json::Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("parse import config: {error}"))?;
    match value.get("language") {
        Some(serde_json::Value::String(language)) => Ok(Some(language.clone())),
        Some(_) => Err("compiler import language must be a string".into()),
        None => Ok(None),
    }
}

pub fn load_compiler_import(config_path: &Path) -> Result<PreparedCompilerImport, String> {
    match import_language(config_path)?.as_deref() {
        Some("c++") => cpp::load_import(config_path)
            .map(|import| PreparedCompilerImport::Program(import.into())),
        Some("rust") => rust::load_import(config_path)
            .map(|import| PreparedCompilerImport::Program(import.into())),
        Some(language) => Err(format!("unsupported compiler import language `{language}`")),
        None => c::compiler_import::load_imports(config_path).map(PreparedCompilerImport::C),
    }
}

/// Explicitly refresh the compiler-owned artifact selected by an import file.
///
/// Existing C configurations have no language field. Typed C++ and Rust
/// boundaries identify themselves explicitly and never fall back to C handling.
pub fn refresh_compiler_import(config_path: &Path) -> Result<(), String> {
    match import_language(config_path)?.as_deref() {
        Some("c++") => cpp::refresh_import(config_path),
        Some("rust") => rust::refresh_import(config_path),
        Some(language) => Err(format!("unsupported compiler import language `{language}`")),
        None => c::compiler_import::create_lock(config_path),
    }
}

/// Immutable compiler-owned inputs shared by the verification tools.
#[derive(Clone, Debug)]
pub enum PreparedProgram {
    Cpp(cpp::PreparedCppImport),
    Rust(rust::PreparedRustImport),
}
impl PreparedProgram {
    pub(crate) fn prepare_execution(&self) -> Result<std::sync::Arc<PreparedExecution>, String> {
        match self {
            Self::Cpp(import) => import.prepared_execution(),
            Self::Rust(import) => import.prepared_execution(),
        }
    }

    pub fn logical_source(&self) -> &str {
        match self {
            Self::Cpp(p) => p.logical_source(),
            Self::Rust(p) => p.logical_source(),
        }
    }
    pub fn identity(&self) -> &str {
        match self {
            Self::Cpp(p) => p.identity(),
            Self::Rust(p) => p.identity(),
        }
    }
    pub fn language(&self) -> SourceLanguage {
        match self {
            Self::Cpp(_) => SourceLanguage::Cpp,
            Self::Rust(_) => SourceLanguage::Rust,
        }
    }
}
impl From<&PreparedProgram> for PreparedProgram {
    fn from(program: &PreparedProgram) -> Self {
        program.clone()
    }
}
impl From<cpp::PreparedCppImport> for PreparedProgram {
    fn from(import: cpp::PreparedCppImport) -> Self {
        Self::Cpp(import)
    }
}
impl From<&cpp::PreparedCppImport> for PreparedProgram {
    fn from(import: &cpp::PreparedCppImport) -> Self {
        Self::Cpp(import.clone())
    }
}
impl From<rust::PreparedRustImport> for PreparedProgram {
    fn from(import: rust::PreparedRustImport) -> Self {
        Self::Rust(import)
    }
}
impl From<&rust::PreparedRustImport> for PreparedProgram {
    fn from(import: &rust::PreparedRustImport) -> Self {
        Self::Rust(import.clone())
    }
}

/// An import's lowered execution, computed on first use. Lowering depends
/// only on the import, so every session over the same import shares it.
#[derive(Debug, Default)]
pub(crate) struct ExecutionCache(std::sync::OnceLock<std::sync::Arc<PreparedExecution>>);

impl ExecutionCache {
    pub(crate) fn get_or_lower(
        &self,
        lower: impl FnOnce() -> Result<std::sync::Arc<PreparedExecution>, String>,
    ) -> Result<std::sync::Arc<PreparedExecution>, String> {
        if let Some(execution) = self.0.get() {
            return Ok(execution.clone());
        }
        let execution = lower()?;
        Ok(self.0.get_or_init(|| execution).clone())
    }
}

/// A frontend's checked execution and contract-facing metadata. Language-specific
/// interpretation is complete before the shared verifier consumes this package.
#[derive(Clone, Debug)]
pub(crate) struct PreparedExecution {
    pub functions: Vec<c::syntax::C0Function>,
    pub layouts: std::collections::BTreeMap<String, c::syntax::C0StructLayout>,
    /// Click `extern` contracts the frontend supplies for library functions
    /// the program calls but does not define, parsed with the sidecar.
    pub library_contracts: String,
}
