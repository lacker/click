//! Experimental safe Rust imports, compiler-owned extraction and direct kernel lowering.
mod charon;
mod crate_inputs;
mod import;
pub(crate) mod lowering;
pub mod names;
mod profile;
pub mod schema;
pub use import::{PreparedRustImport, load_import, refresh_import};

/// Prepare the same contract-facing execution package as the other typed frontend.
pub(crate) fn prepare_execution(
    import: &PreparedRustImport,
) -> Result<std::sync::Arc<crate::languages::PreparedExecution>, String> {
    let (functions, layouts) = lowering::lower(import.export())?;
    Ok(std::sync::Arc::new(crate::languages::PreparedExecution {
        functions,
        layouts,
        library_contracts: String::new(),
    }))
}
