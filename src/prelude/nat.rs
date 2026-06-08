//! Nat source for the standard prelude.

pub(super) const CORE_SOURCE: &str = include_str!("nat/core.lisp");
pub(super) const ORDER_SOURCE: &str = include_str!("nat/order.lisp");
pub(super) const ADD_SOURCE: &str = include_str!("nat/add.lisp");
pub(super) const SUB_SOURCE: &str = include_str!("nat/sub.lisp");
pub(super) const MUL_SOURCE: &str = include_str!("nat/mul.lisp");

pub(super) const SOURCES: &[(&str, &str)] = &[
    ("nat/core", CORE_SOURCE),
    ("nat/order", ORDER_SOURCE),
    ("nat/add", ADD_SOURCE),
    ("nat/sub", SUB_SOURCE),
    ("nat/mul", MUL_SOURCE),
];
