//! How diagnostics print the places of a function whose sidecar signature is
//! written in Rust syntax.

use super::*;

thread_local! {
    /// The slice parameters of the function being checked when its
    /// signature is written in Rust syntax; `None` for the C-shaped spelling.
    static RUST_SPELLING: std::cell::RefCell<Option<std::rc::Rc<[String]>>> =
        const { std::cell::RefCell::new(None) };
}

/// Prints the places of a function whose signature is written in Rust
/// syntax as its sidecar writes them: a slice's length `bytes.len()`, a cast
/// `(value as u32)`, and a field through a reference `p.field`. Like the
/// ambient naming, it stays set after the function's check, for a failure
/// rendered later; the next declaration replaces it. The parser reads each
/// form back in such a function, so `click expand` prints through it too.
pub(crate) fn enter_rust_spelling(signature: Option<&super::FunctionSignature>) {
    let spelling = signature
        .and_then(super::FunctionSignature::rust_slice_parameters)
        .map(std::rc::Rc::<[String]>::from);
    RUST_SPELLING.with(|slot| *slot.borrow_mut() = spelling);
}

/// The slice parameters of the function whose places are printed, when its
/// signature is written in Rust syntax: an expansion's own function, else
/// the function last checked.
pub(super) fn rust_slice_parameters() -> Option<std::rc::Rc<[String]>> {
    REFERENCE_CARRIERS
        .with(|scopes| {
            scopes
                .borrow()
                .iter()
                .rev()
                .find_map(|scope| scope.rust_spelling.clone())
        })
        .unwrap_or_else(|| RUST_SPELLING.with(|slot| slot.borrow().clone()))
}

pub(crate) fn rust_spelling() -> bool {
    rust_slice_parameters().is_some()
}

/// The Rust spelling of the variable `name`: `bytes.len()` for the length
/// of the slice parameter `bytes`.
pub(crate) fn rust_variable_spelling(name: &str) -> Option<String> {
    let slice = name.strip_suffix("_len")?;
    rust_slice_parameters()?
        .iter()
        .any(|known| known == slice)
        .then(|| format!("{slice}.len()"))
}

/// The Rust name of the scalar type `c_type`, `u32` for `uint32`.
pub(super) fn rust_scalar_spelling(c_type: &CType) -> Option<&'static str> {
    Some(match c_type {
        CType::Int8 => "i8",
        CType::Int16 => "i16",
        CType::Int32 => "i32",
        CType::UInt8 => "u8",
        CType::UInt16 => "u16",
        CType::UInt32 => "u32",
        CType::Int64 => "i64",
        CType::UInt64 => "u64",
        CType::Int128 => "i128",
        CType::UInt128 => "u128",
        _ => return None,
    })
}
