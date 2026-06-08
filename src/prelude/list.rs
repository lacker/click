//! List source for the standard prelude.

pub(super) const CORE_SOURCE: &str = include_str!("list/core.lisp");
pub(super) const BOOLEANS_SOURCE: &str = include_str!("list/booleans.lisp");
pub(super) const OPERATIONS_SOURCE: &str = include_str!("list/operations.lisp");
pub(super) const VALUE_EQ_SOURCE: &str = include_str!("list/value_eq.lisp");
pub(super) const DERIVED_SOURCE: &str = include_str!("list/derived.lisp");

pub(super) const SOURCES: &[&str] = &[
    CORE_SOURCE,
    BOOLEANS_SOURCE,
    OPERATIONS_SOURCE,
    VALUE_EQ_SOURCE,
    DERIVED_SOURCE,
];
