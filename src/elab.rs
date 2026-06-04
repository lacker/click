//! Source elaboration layered between surface syntax and the kernel.

pub(crate) mod loader;
pub(crate) mod proof;
pub(crate) mod source;
pub(crate) mod tactics;

pub use loader::{LoadedSource, SourceComputationError, SourceFileLoadError, SourceLoadError};
pub use proof::{EvaluationProofError, ProofElaborationError, SourceTheoremError};
pub use source::{ElabEnv, ParseError};
