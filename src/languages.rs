//! Program languages supported by Surface Click.

use std::fs;
use std::path::Path;

pub mod c;
pub(crate) mod compiler_process;
pub mod cpp;

#[derive(Clone, Debug)]
pub enum PreparedCompilerImport {
    C(Vec<c::compiler_import::PreparedCImport>),
    Cpp(cpp::PreparedCppImport),
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
        Some("c++") => cpp::load_import(config_path).map(PreparedCompilerImport::Cpp),
        Some(language) => Err(format!("unsupported compiler import language `{language}`")),
        None => c::compiler_import::load_imports(config_path).map(PreparedCompilerImport::C),
    }
}

/// Explicitly refresh the compiler-owned artifact selected by an import file.
///
/// Existing C configurations have no language field. The new typed C++
/// boundary identifies itself explicitly and never falls back to C handling.
pub fn refresh_compiler_import(config_path: &Path) -> Result<(), String> {
    match import_language(config_path)?.as_deref() {
        Some("c++") => cpp::refresh_import(config_path),
        Some(language) => Err(format!("unsupported compiler import language `{language}`")),
        None => c::compiler_import::create_lock(config_path),
    }
}
