//! Source elaboration layered between surface syntax and the kernel.

pub(crate) mod proof;
pub(crate) mod source;

pub use proof::{EvaluationProofError, ProofElaborationError, SourceTheoremError};
pub use source::{ElabEnv, ParseError};
