//! Experimental rich kernel for systems-code proofs.
//!
//! This module keeps the LCF shape: `Theorem` is an abstract object whose
//! constructor is not public. Public theorem constructors in this module are
//! Click axioms: trusted built-in operations that produce theorem objects
//! directly.
//!
//! The kernel is currently a single Rust module split across several files with
//! `include!`. That keeps this refactor mechanical: private helper visibility
//! remains exactly as it was in the old `megakernel.rs`, while the physical
//! layout is small enough to navigate.

use std::collections::{BTreeMap, BTreeSet};

include!("primitives.rs");
include!("assumptions.rs");
include!("api.rs");
include!("reasoning.rs");
include!("spec.rs");
include!("eval.rs");
include!("loops.rs");
include!("functions.rs");
include!("tests.rs");
