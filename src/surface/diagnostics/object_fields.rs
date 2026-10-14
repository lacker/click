//! Field spellings for constant offsets into struct-typed globals.
//!
//! A memory-history sentence names a cell by its address. An address a
//! constant number of bytes into a struct-typed global otherwise prints as
//! `g+8`; where exactly one scalar field of the global's declared layout
//! occupies exactly the bytes the access covers, the cell is that field,
//! `g.payload.number`. A union whose members share an offset and width, an
//! array member, or an access whose width matches no field keeps the offset.
//!
//! A struct-typed local keeps the offset: the function's table of local
//! struct types is keyed by source spelling, while a local's block carries
//! its kernel name, and a shadowing declaration of another type can hold
//! the block that spelling would find. A global's block is its unique kernel
//! name.
//!
//! Diagnostics only: nothing a check decides reads these spellings. The table
//! is built when a function's verification starts, from its declarations.

use super::*;

/// One scalar field of an object: its byte offset inside the object, its
/// width, and its member path (`payload.number`).
struct ObjectField {
    offset: u32,
    width: u32,
    path: String,
}

/// The source name and scalar fields of each struct-typed global, by the
/// kernel block that holds it.
type ObjectFields = std::collections::HashMap<String, (String, Vec<ObjectField>)>;

thread_local! {
    static AMBIENT_OBJECT_FIELDS: std::cell::RefCell<Option<std::rc::Rc<ObjectFields>>> =
        const { std::cell::RefCell::new(None) };
}

/// Starts naming the struct-typed globals `function` can reach.
pub(crate) fn enter_ambient_object_fields(function: &syntax::C0Function) {
    let mut objects = ObjectFields::new();
    for aggregate in function.global_aggregates().values() {
        let block = if aggregate.kernel_name().starts_with("global:") {
            aggregate.kernel_name().to_string()
        } else {
            format!("global:{}", aggregate.kernel_name())
        };
        let mut fields = Vec::new();
        collect_struct_fields(function, aggregate.layout(), "", 0, &mut fields, 0);
        objects.insert(block, (aggregate.name().to_string(), fields));
    }
    AMBIENT_OBJECT_FIELDS.with(|slot| *slot.borrow_mut() = Some(std::rc::Rc::new(objects)));
}

pub(crate) fn clear_ambient_object_fields() {
    AMBIENT_OBJECT_FIELDS.with(|slot| *slot.borrow_mut() = None);
}

/// How deep embedded structs and unions are followed.
const MAX_NESTING: usize = 8;

/// A scalar field's width, when its declared type is one: arrays, embedded
/// aggregates and `long double` are not single cells a width can match.
fn scalar_width(c_type: C0Type, byte_width: u32, long_double: bool) -> Option<u32> {
    let width = match c_type {
        C0Type::Bool | C0Type::Char(_) | C0Type::Int8 | C0Type::UInt8 => 1,
        C0Type::Int16 | C0Type::UInt16 => 2,
        C0Type::Int32 | C0Type::UInt32 | C0Type::Float32 => 4,
        C0Type::Int64(_) | C0Type::UInt64(_) | C0Type::Float64 => 8,
        _ if c_type.is_pointer() => 8,
        _ => return None,
    };
    (!long_double && width == byte_width).then_some(width)
}

fn collect_struct_fields(
    function: &syntax::C0Function,
    layout: &syntax::C0StructLayout,
    prefix: &str,
    base: u32,
    out: &mut Vec<ObjectField>,
    depth: usize,
) {
    if depth > MAX_NESTING {
        return;
    }
    for (name, field) in layout.fields() {
        let path = format!("{prefix}{name}");
        let Some(offset) = base.checked_add(field.offset_bytes()) else {
            continue;
        };
        if field.array_shape().is_some() || field.array_element_width().is_some() {
            continue;
        }
        if let Some(nested) = field.struct_name() {
            if let Some(nested) = function.structs().get(nested) {
                collect_struct_fields(
                    function,
                    nested,
                    &format!("{path}."),
                    offset,
                    out,
                    depth + 1,
                );
            }
        } else if let Some(union) = field.union_name() {
            if let Some(union) = function.unions().get(union) {
                collect_union_fields(function, union, &format!("{path}."), offset, out, depth + 1);
            }
        } else if let Some(width) =
            scalar_width(field.c_type(), field.byte_width(), field.is_long_double())
        {
            out.push(ObjectField {
                offset,
                width,
                path,
            });
        }
    }
}

fn collect_union_fields(
    function: &syntax::C0Function,
    layout: &syntax::C0UnionLayout,
    prefix: &str,
    base: u32,
    out: &mut Vec<ObjectField>,
    depth: usize,
) {
    if depth > MAX_NESTING {
        return;
    }
    for (name, field) in layout.fields() {
        let path = format!("{prefix}{name}");
        let Some(offset) = base.checked_add(field.offset_bytes()) else {
            continue;
        };
        if field.array_shape().is_some() {
            continue;
        }
        if let Some(nested) = field.struct_name() {
            if let Some(nested) = function.structs().get(nested) {
                collect_struct_fields(
                    function,
                    nested,
                    &format!("{path}."),
                    offset,
                    out,
                    depth + 1,
                );
            }
        } else if let Some(width) =
            scalar_width(field.c_type(), field.byte_width(), field.is_long_double())
        {
            out.push(ObjectField {
                offset,
                width,
                path,
            });
        }
    }
}

/// The field spelling of the `width` bytes at `offset` into the global in
/// `block`, when exactly one scalar field occupies exactly those bytes.
pub(super) fn object_field_spelling(block: &str, offset: u32, width: u32) -> Option<String> {
    AMBIENT_OBJECT_FIELDS.with(|slot| {
        let slot = slot.borrow();
        let (name, fields) = slot.as_ref()?.get(block)?;
        let mut matching = fields
            .iter()
            .filter(|field| field.offset == offset && field.width == width);
        let field = matching.next()?;
        matching
            .next()
            .is_none()
            .then(|| format!("{name}.{}", field.path))
    })
}
