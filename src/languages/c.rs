//! The C0 program-language frontend and source model.

pub(crate) mod address_taken;
pub mod compiler_import;
pub(crate) mod provenance;
pub mod source;
pub mod syntax;
pub mod target;

#[cfg(test)]
mod tests;
