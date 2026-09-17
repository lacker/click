//! The C0 program-language frontend and source model.

pub mod compiler_import;
pub(crate) mod provenance;
pub mod source;
pub mod syntax;
pub mod target;
pub(crate) mod threads;

#[cfg(test)]
mod tests;
