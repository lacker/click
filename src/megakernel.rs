//! Compatibility facade for the proof kernel.
//!
//! New code should prefer `crate::kernel`; this module exists for legacy
//! external callers that still import `crate::megakernel`.

pub use crate::kernel::*;
