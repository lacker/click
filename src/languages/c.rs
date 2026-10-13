//! The C0 program-language frontend and source model.

pub(crate) mod address_taken;
pub mod compiler_import;
pub(crate) mod integer_specifiers;
pub(crate) mod option_profile;
pub(crate) mod projection;
pub(crate) mod provenance;
pub mod source;
pub mod syntax;
pub(crate) mod system_headers;
pub mod target;
pub mod thread_runtime;

#[cfg(test)]
mod linux_rbtree_tests;
#[cfg(test)]
mod tests;
