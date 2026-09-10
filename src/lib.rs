// Proof and kernel operations intentionally pass explicit contexts, while the
// recursive proof AST and validity errors favor direct values over pervasive
// boxing. Keep these structural tradeoffs explicit while denying other Clippy
// warnings in CI and local development.
#![allow(clippy::large_enum_variant)]
#![allow(clippy::result_large_err)]
#![allow(clippy::too_many_arguments)]
// Interned kernel terms carry `Arc`-shared memo cells, so every set and map
// keyed by a term looks mutable to Clippy. The cells are content-derived
// caches that never change a key's hash or ordering.
#![allow(clippy::mutable_key_type)]
// Kernel proof types name their obligation, presentation, and execution
// parameters explicitly; a `type` alias would hide exactly the parameters a
// reviewer has to check.
#![allow(clippy::type_complexity)]
// Proof structures are thread-local by construction and share their
// substructure through `Arc` without ever crossing a thread boundary.
#![allow(clippy::arc_with_non_send_sync)]

pub mod cli;
pub mod instrumentation;
pub mod kernel;
pub mod languages;
mod persistent;
mod source;
pub mod surface;
