// Proof and kernel operations intentionally pass explicit contexts, while the
// recursive proof AST and validity errors favor direct values over pervasive
// boxing. Keep these structural tradeoffs explicit while denying other Clippy
// warnings in CI and local development.
#![allow(clippy::large_enum_variant)]
#![allow(clippy::result_large_err)]
#![allow(clippy::too_many_arguments)]

pub mod cli;
pub mod instrumentation;
pub mod kernel;
pub mod lang;
mod persistent;
