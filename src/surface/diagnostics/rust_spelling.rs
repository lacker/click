//! How diagnostics print the places of a function whose sidecar signature is
//! written in Rust syntax.

use super::*;
use crate::languages::interface::RustLoopIterator;

#[derive(Default)]
pub(super) struct RustLoopSpelling {
    iterators: std::sync::Arc<[Option<RustLoopIterator>]>,
    /// The bindings that hold a loop iterator's own fields, each of which a
    /// proof names through an `iter` accessor.
    iterator_fields: std::collections::BTreeSet<crate::kernel::BindingName>,
}

impl RustLoopSpelling {
    pub(super) fn of(signature: &super::FunctionSignature) -> Self {
        let iterators = signature.rust_loop_iterators().clone();
        let iterator_fields = iterators
            .iter()
            .flatten()
            .flat_map(|iterator| {
                iterator
                    .chunk_fields
                    .iter()
                    .flat_map(|fields| fields.bindings().into_iter().cloned())
                    .chain(
                        iterator
                            .slice_fields
                            .iter()
                            .map(|fields| fields.slice.clone()),
                    )
                    .chain(iterator.count_binding.iter().cloned())
                    .chain(iterator.range_bounds.iter().flatten().cloned())
                    .collect::<Vec<_>>()
            })
            .collect();
        Self {
            iterators,
            iterator_fields,
        }
    }
}

thread_local! {
    /// The slice parameters of the function being checked when its
    /// signature is written in Rust syntax; `None` for the C-shaped spelling.
    static RUST_SPELLING: std::cell::RefCell<Option<std::rc::Rc<[String]>>> =
        const { std::cell::RefCell::new(None) };
    /// The iterator each loop of that function advances.
    static RUST_LOOP_SPELLING: std::cell::RefCell<RustLoopSpelling> =
        std::cell::RefCell::new(RustLoopSpelling::default());
    /// The loop whose phases are being checked, whose iterator a proof
    /// there names bare `iter`.
    static CURRENT_LOOP: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
    /// The pure functions whose result is a slice, with the slice's element
    /// type: a call's data pointer is `f(x).as_ptr()`.
    static SLICE_RESULT_FUNCTIONS: std::cell::RefCell<
        std::collections::BTreeMap<String, crate::kernel::SliceElement>,
    > = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
}

/// Records that the pure function `name` returns a slice of `element`, so the
/// data pointer of a call, which the kernel bases on the application
/// (`design/rust-slice-values.md`, step 2b-iii-b-ii), is spelled
/// `f(x).as_ptr()` and never as the call, which is the slice.
pub(crate) fn record_slice_result_function(name: &str, element: crate::kernel::SliceElement) {
    SLICE_RESULT_FUNCTIONS.with(|slot| {
        slot.borrow_mut().insert(name.to_string(), element);
    });
}

/// The element type of the slice the pure function `name` returns, or of
/// an instance of it, `f::<uint8>`; `None` for a function that returns no
/// slice.
pub(crate) fn slice_result_element(name: &str) -> Option<crate::kernel::SliceElement> {
    let name = name.split("::<").next().unwrap_or(name);
    SLICE_RESULT_FUNCTIONS.with(|slot| slot.borrow().get(name).copied())
}

/// `left, right` split at its one top-level comma.
fn split_top_level_pair(text: &str) -> Option<(&str, &str)> {
    let mut depth = 0usize;
    for (index, character) in text.char_indices() {
        match character {
            '(' | '[' => depth += 1,
            ')' | ']' => depth = depth.checked_sub(1)?,
            ',' if depth == 0 => {
                return Some((&text[..index], text[index + 1..].trim_start()));
            }
            _ => {}
        }
    }
    None
}

/// The subslice a constructed slice with data `pointer` and length `length`
/// was built as, `bytes[a..b]`, `bytes[a..]` or `bytes[..b]`, for a value the
/// kernel recorded as constructed under a subslice's bounds.
pub(crate) fn subslice_spelling(pointer: &str, length: &str) -> Option<String> {
    let (pointer, length) = (unparenthesized(pointer), unparenthesized(length));
    let (base, start) = match pointer
        .strip_prefix('&')
        .and_then(|element| element.strip_suffix(']'))
        .and_then(|element| element.rsplit_once('['))
    {
        Some((base, start)) => (base, Some(start)),
        None => match pointer.split_once(" + ") {
            Some((base, start)) => (base, Some(start)),
            None => (pointer, None),
        },
    };
    let (slice, own_lengths) = slice_with_data(base)?;
    // The length a subslice was built with, `end - start`, gives back its
    // end; the slice's own length is an open end.
    let start = start.map(usize_bound);
    let end = match &start {
        Some(start) => [start.clone(), format!("{start}u64")]
            .iter()
            .find_map(|start| length.strip_suffix(&format!(" - {start}")))
            .map(unparenthesized)
            .map_or_else(
                || {
                    start
                        .parse::<u64>()
                        .ok()
                        .zip(usize_bound(length).parse::<u64>().ok())
                        .and_then(|(start, length)| start.checked_add(length))
                        .map_or_else(|| format!("{start} + {length}"), |end| end.to_string())
                },
                str::to_string,
            ),
        None => length.to_string(),
    };
    let end = (!own_lengths.contains(&end)).then(|| usize_bound(&end));
    if start.is_none() && end.is_none() {
        return Some(slice);
    }
    Some(format!(
        "{slice}[{}..{}]",
        start.unwrap_or_default(),
        end.unwrap_or_default()
    ))
}

/// The slice whose data pointer is spelled `pointer`, `x.as_ptr()`, with
/// the spelling of its own length.
fn slice_with_data(pointer: &str) -> Option<(String, Vec<String>)> {
    let slice = pointer.strip_suffix(".as_ptr()")?;
    Some((slice.to_string(), vec![format!("{slice}.len()")]))
}

/// A subslice bound as written: `usize`, so a numeral needs no suffix.
fn usize_bound(bound: &str) -> String {
    let bound = unparenthesized(bound);
    match bound.strip_suffix("u64") {
        Some(digits) if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) => {
            digits.to_string()
        }
        _ => bound.to_string(),
    }
}

/// `text` without parentheses that enclose all of it.
fn unparenthesized(text: &str) -> &str {
    let Some(inner) = text
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return text;
    };
    let mut depth = 0usize;
    for character in inner.chars() {
        match character {
            '(' => depth += 1,
            ')' if depth == 0 => return text,
            ')' => depth -= 1,
            _ => {}
        }
    }
    if depth == 0 { inner } else { text }
}

/// While it lives, loop `index`'s phases are being checked: its iterator's
/// state is printed `iter.len()`, every other loop's `loop(i).iter.len()`.
pub(crate) struct LoopPhaseSpelling(Option<usize>);

impl LoopPhaseSpelling {
    pub(crate) fn enter(index: usize) -> Self {
        Self(CURRENT_LOOP.with(|slot| slot.replace(Some(index))))
    }
}

impl Drop for LoopPhaseSpelling {
    fn drop(&mut self) {
        CURRENT_LOOP.with(|slot| slot.set(self.0));
    }
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
    let loops = signature.map(RustLoopSpelling::of).unwrap_or_default();
    RUST_LOOP_SPELLING.with(|slot| *slot.borrow_mut() = loops);
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

/// The iterator metadata of the function whose proof is being printed.
fn with_rust_loop_spelling<T>(read: impl FnOnce(&RustLoopSpelling) -> T) -> T {
    REFERENCE_CARRIERS.with(|scopes| {
        let scopes = scopes.borrow();
        if let Some(loops) = scopes
            .iter()
            .rev()
            .find_map(|scope| scope.rust_loop_spelling.as_ref())
        {
            return read(loops);
        }
        RUST_LOOP_SPELLING.with(|slot| read(&slot.borrow()))
    })
}

/// The spelling of the program variable `name` where its bare name is not
/// its own, such as `program::iterations` for a variable named like a loop's pass count,
/// which the bare name means wherever it is written. A variable named
/// `result` is not rewritten here: the same name also carries the contract
/// result, so raising decides at the binding's origin.
pub(crate) fn rust_variable_spelling(name: &str) -> Option<String> {
    if name == crate::surface::LOOP_ITERATIONS_NAME {
        return Some(format!("program::{name}"));
    }
    with_rust_loop_spelling(|loops| {
        crate::surface::rust_iterator_spelling(
            &loops.iterators,
            CURRENT_LOOP.with(std::cell::Cell::get),
            &name.into(),
        )
    })
}

/// Render a program binding through its existing iterator or slice accessors.
pub(crate) fn rust_binding_spelling(name: &crate::kernel::BindingName) -> Option<String> {
    if let Some(name) = name.named() {
        return rust_variable_spelling(name);
    }
    if !name
        .local_id()
        .is_some_and(crate::kernel::LocalBindingId::is_iterator_field)
    {
        return None;
    }
    with_rust_loop_spelling(|loops| {
        crate::surface::rust_iterator_spelling(
            &loops.iterators,
            CURRENT_LOOP.with(std::cell::Cell::get),
            name,
        )
    })
}

/// Only the loop's iterator fields have selectors. Raise the values held
/// by iterator copies, such as a slice iterator an `enumerate` wraps, and
/// the private Option fields structurally.
pub(crate) fn has_surface_iterator_binding(name: &crate::kernel::BindingName) -> bool {
    let Some(id) = name.local_id() else {
        return true;
    };
    !id.is_iterator_option_field()
        && (!id.is_iterator_field()
            || with_rust_loop_spelling(|loops| loops.iterator_fields.contains(name)))
}

/// The Rust name of the scalar type `interface_type`, `u32` for `uint32`.
pub(super) fn rust_scalar_spelling(interface_type: &ProgramType) -> Option<&'static str> {
    Some(match interface_type {
        ProgramType::Int8 => "i8",
        ProgramType::Int16 => "i16",
        ProgramType::Int32 => "i32",
        ProgramType::UInt8 => "u8",
        ProgramType::UInt16 => "u16",
        ProgramType::UInt32 => "u32",
        ProgramType::Int64 => "i64",
        ProgramType::UInt64 => "u64",
        ProgramType::Int128 => "i128",
        ProgramType::UInt128 => "u128",
        _ => return None,
    })
}

/// A call of the built-in slice type's operations in the Rust spelling
/// (`design/rust-slice-values.md`): `x.len()`, `x.as_ptr()`, `x[a..b]` and
/// `slice::from_raw_parts(p, n)`. `name` may carry the qualified path and an instance,
/// `click::rust::slice::len::<uint8>`.
pub(crate) fn slice_call_spelling(name: &str, arguments: &[String]) -> Option<String> {
    // Only a function written in Rust syntax reads Rust's slice methods
    // back; elsewhere the library call is its own spelling.
    if !rust_spelling() {
        return None;
    }
    let base = name.split("::<").next().unwrap_or(name);
    // A string slice's operations are `str`'s methods.
    if let Some(method) = base.strip_prefix("click::rust::str::") {
        return match (method, arguments) {
            ("len" | "as_ptr", [string]) => Some(format!("{string}.{method}()")),
            // The byte view is the library call: a `fn`'s `&str` parameter
            // has only `len()` and `as_ptr()` as methods, so `s.as_bytes()`
            // would not lower back there (`design/rust-slice-values.md`,
            // step 3c-ii).
            ("as_bytes", [string]) => Some(format!("click::rust::str::as_bytes({string})")),
            ("from_utf8_unchecked", [bytes]) => {
                Some(format!("click::rust::str::from_utf8_unchecked({bytes})"))
            }
            _ => None,
        };
    }
    let method = base
        .strip_prefix("click::rust::slice::")
        .or_else(|| base.strip_prefix("slice::"))?;
    match (method, arguments) {
        ("len", [slice]) => Some(format!("{}.len()", slice_receiver(slice))),
        ("as_ptr", [slice]) => Some(format!("{slice}.as_ptr()")),
        ("from_raw_parts", [pointer, length]) => Some(format!(
            "click::rust::slice::from_raw_parts({pointer}, {length})"
        )),
        ("subslice", [slice, start, end]) => Some(subslice_of(slice_receiver(slice), start, end)),
        _ => None,
    }
}

/// A slice spelled `slice` as the receiver of a Rust slice method: a slice
/// parameter's own slice, `slice::from_raw_parts(bytes, bytes.len())`, is
/// the parameter, `bytes`, which the parser reads there as that slice
/// (`design/rust-slice-values.md`, until step 3).
fn slice_receiver(slice: &str) -> &str {
    slice
        .strip_prefix("click::rust::slice::from_raw_parts(")
        .and_then(|rest| rest.strip_suffix(')'))
        .and_then(split_top_level_pair)
        .filter(|(pointer, length)| {
            !pointer.ends_with(".as_ptr()")
                && slice_with_data(pointer).is_some_and(|(_, lengths)| {
                    lengths.iter().any(|own| own == unparenthesized(length))
                })
        })
        .map_or(slice, |(pointer, _)| pointer)
}

/// The subslice `slice[start..end]` as written: a start of `0` and an end of
/// the slice's own length are left out, `bytes[..2]` and `bytes[1..]`.
fn subslice_of(slice: &str, start: &str, end: &str) -> String {
    let start = usize_bound(start);
    let start = if start == "0" { String::new() } else { start };
    let end = if unparenthesized(end) == format!("{slice}.len()") {
        String::new()
    } else {
        usize_bound(end)
    };
    format!("{slice}[{start}..{end}]")
}
