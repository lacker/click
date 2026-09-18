//! Dev-only `sorry` proof hole: flag storage.
//!
//! The flag lives here (not in the surface layer) so the kernel primitive
//! that closes a goal as admitted can gate creation itself. The surface
//! layer decides *where* `sorry` may appear (complete contract bodies and
//! complete `have` bodies only); this flag decides *whether* the kernel will
//! construct the admission at all. Both gates must pass. Nothing outside
//! `click verify --allow-sorry` sets this flag.

use std::cell::Cell;

thread_local! {
    static ALLOW_SORRY: Cell<bool> = const { Cell::new(false) };
}

/// Whether the kernel may close a goal as admitted via `sorry`.
pub(crate) fn sorry_is_allowed() -> bool {
    ALLOW_SORRY.with(Cell::get)
}

/// Sets the flag, returning the previous value for scoped restore.
pub(crate) fn set_sorry_allowed(value: bool) -> bool {
    ALLOW_SORRY.with(|allowed| allowed.replace(value))
}
