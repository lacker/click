//! The C0 program-language frontend and source model.

pub mod compiler_import;
pub(crate) mod provenance;
pub mod source;
pub mod syntax;
pub mod target;

mod compiler_process;

#[cfg(test)]
mod tests;
