//! Nat source for the standard prelude.

pub(super) const CORE_SOURCE: &str = include_str!("nat/core.lisp");
pub(super) const ORDER_SOURCE: &str = include_str!("nat/order.lisp");
pub(super) const ADD_SOURCE: &str = include_str!("nat/add.lisp");
pub(super) const SUB_SOURCE: &str = include_str!("nat/sub.lisp");
pub(super) const MUL_SOURCE: &str = include_str!("nat/mul.lisp");

pub(super) const SOURCES: &[&str] = &[
    CORE_SOURCE,
    ORDER_SOURCE,
    ADD_SOURCE,
    SUB_SOURCE,
    MUL_SOURCE,
];
