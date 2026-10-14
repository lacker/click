//! The axiomatic C++ standard-library boundary: model accessors that name a
//! standard type's abstract state, and the contracts Click supplies for the
//! standard functions a program calls.
//!
//! A proof states a standard-library type's state through model accessors,
//! such as `std_span_data(s)` and `std_span_size(s)`, never through a
//! library's private fields. Each accessor is a spelling for one field path,
//! and the binding below for the library that was parsed is the only place
//! that names those fields. The parser rewrites an accessor application into
//! its field path, so the result is checked like any written field access.

use std::collections::BTreeMap;

use crate::languages::c::syntax::C0StructLayout;

/// One model accessor bound to a field path in one library's record.
struct AccessorBinding {
    /// The prefix of the record's name, which names its template.
    record_prefix: &'static str,
    accessor: &'static str,
    path: &'static [&'static str],
}

/// libstdc++: `std::span<T>` holds `_M_ptr` and an extent storage whose
/// dynamic value is `_M_extent_value`. libc++: a dynamic-extent
/// `std::span<T>` holds `__data_` and `__size_`.
const BINDINGS: &[AccessorBinding] = &[
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_data",
        path: &["_M_ptr"],
    },
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_size",
        path: &["_M_extent", "_M_extent_value"],
    },
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_data",
        path: &["__data_"],
    },
    AccessorBinding {
        record_prefix: "span__",
        accessor: "std_span_size",
        path: &["__size_"],
    },
    // `std::array<T, N>` holds its elements in `T _M_elems[N]` (libstdc++)
    // or `T __elems_[N]` (libc++).
    AccessorBinding {
        record_prefix: "array__",
        accessor: "std_array_data",
        path: &["_M_elems"],
    },
    AccessorBinding {
        record_prefix: "array__",
        accessor: "std_array_data",
        path: &["__elems_"],
    },
];

/// The model accessors the parsed records support, each with its field path.
/// An accessor is available when some record of its template has a bound
/// path; a library whose layout matches no binding binds none, and records
/// that match more than one binding of an accessor bind it to neither, so an
/// accessor is never misbound.
pub(crate) fn model_accessors(
    layouts: &BTreeMap<String, C0StructLayout>,
) -> BTreeMap<&'static str, &'static [&'static str]> {
    let mut accessors = BTreeMap::new();
    let mut ambiguous = Vec::new();
    for binding in BINDINGS {
        let bound = layouts.iter().any(|(name, layout)| {
            name.starts_with(binding.record_prefix) && has_path(layouts, layout, binding.path)
        });
        if bound && accessors.insert(binding.accessor, binding.path).is_some() {
            ambiguous.push(binding.accessor);
        }
    }
    for accessor in ambiguous {
        accessors.remove(accessor);
    }
    accessors
}

fn has_path(
    layouts: &BTreeMap<String, C0StructLayout>,
    layout: &C0StructLayout,
    path: &[&str],
) -> bool {
    let Some((first, rest)) = path.split_first() else {
        return true;
    };
    let Some(field) = layout.field(first) else {
        return false;
    };
    if rest.is_empty() {
        return true;
    }
    field
        .struct_name()
        .and_then(|name| layouts.get(name))
        .is_some_and(|inner| has_path(layouts, inner, rest))
}

/// A standard function Click has a contract for, keyed on its qualified name
/// and canonical signature as Clang spells them. The contract is a template:
/// `{name}` is the function's proof name, `{record}` its receiver's record,
/// and `{p1}`, `{p2}`, ... its parameters after the receiver, as the
/// interface names them.
///
/// An entry over `std::span<T>` is generic in its element: `{T}` in the
/// qualified name and `{T_signature}` in the signature are the element as
/// Clang spells it there, `{element}` is its Click type, and `{bytes}` its
/// size. An element outside [`SPAN_ELEMENTS`] matches no entry, so a call is
/// refused by name.
struct CatalogEntry {
    qualified_name: &'static str,
    signature: &'static str,
    contract: &'static str,
}

/// A `std::span` element type the catalog can state contracts for.
struct SpanElement {
    /// The element as Clang spells it in a qualified name.
    name: &'static str,
    /// The element as Clang spells it in a canonical signature.
    signature: &'static str,
    /// The element's Click type.
    click: &'static str,
    /// `sizeof` the element.
    bytes: u64,
}

const SPAN_ELEMENTS: &[SpanElement] = &[
    SpanElement {
        name: "int",
        signature: "int",
        click: "int32",
        bytes: 4,
    },
    SpanElement {
        name: "unsigned int",
        signature: "unsigned int",
        click: "uint32",
        bytes: 4,
    },
    SpanElement {
        name: "unsigned char",
        signature: "unsigned char",
        click: "uint8",
        bytes: 1,
    },
    SpanElement {
        name: "std::byte",
        signature: "enum std::byte",
        click: "uint8",
        bytes: 1,
    },
    SpanElement {
        name: "const int",
        signature: "const int",
        click: "const int32",
        bytes: 4,
    },
    SpanElement {
        name: "const unsigned int",
        signature: "const unsigned int",
        click: "const uint32",
        bytes: 4,
    },
    SpanElement {
        name: "const unsigned char",
        signature: "const unsigned char",
        click: "const uint8",
        bytes: 1,
    },
    SpanElement {
        name: "const std::byte",
        signature: "const enum std::byte",
        click: "const uint8",
        bytes: 1,
    },
];

/// The value of `std::dynamic_extent`, which `subspan` takes as its count
/// for "to the end".
const DYNAMIC_EXTENT: &str = "18446744073709551615u64";

// `std::span<T>` with dynamic extent: a view of `[data, data + size)`. The
// element accessors require an index inside the view, which the standard
// makes a precondition; they form an address and read nothing. The
// subview operations require the subview to lie inside the view, as the
// standard does, and keep the backing storage.
const SPAN_CATALOG: &[CatalogEntry] = &[
    CatalogEntry {
        qualified_name: "std::span<{T}>::size",
        signature: "unsigned long (void) const noexcept",
        contract: "extern uint64 {name}(const struct {record}* this) {
    views std_span_size(this);
    ensures result == std_span_size(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::size_bytes",
        signature: "unsigned long (void) const noexcept",
        contract: "extern uint64 {name}(const struct {record}* this) {
    views std_span_size(this);
    ensures result == std_span_size(this) * {bytes}u64;
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::data",
        signature: "{T_signature} *(void) const noexcept",
        contract: "extern {element}* {name}(const struct {record}* this) {
    views std_span_data(this);
    ensures result == std_span_data(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::front",
        signature: "{T_signature} &(void) const noexcept",
        contract: "extern {element}& {name}(const struct {record}* this) {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::back",
        signature: "{T_signature} &(void) const noexcept",
        contract: "extern {element}& {name}(const struct {record}* this) {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this) + (std_span_size(this) - 1u64);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::operator[]",
        signature: "{T_signature} &(unsigned long) const noexcept",
        contract: "extern {element}& {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    views std_span_size(this);
    requires {p1} < std_span_size(this);
    ensures &result == std_span_data(this) + {p1};
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::first",
        signature: "class std::span<{T_signature}> (unsigned long) const noexcept",
        contract: "extern struct {record} {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    views std_span_size(this);
    requires {p1} <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == {p1};
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::last",
        signature: "class std::span<{T_signature}> (unsigned long) const noexcept",
        contract: "extern struct {record} {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    views std_span_size(this);
    requires {p1} <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this) + (std_span_size(this) - {p1});
    ensures std_span_size(result) == {p1};
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}>::subspan",
        signature: "class std::span<{T_signature}> (unsigned long, unsigned long) const noexcept",
        contract:
            "extern struct {record} {name}(const struct {record}* this, uint64 {p1}, uint64 {p2}) {
    views std_span_data(this);
    views std_span_size(this);
    requires {p1} <= std_span_size(this);
    requires {p2} != {dynamic_extent} implies {p2} <= std_span_size(this) - {p1};
    ensures std_span_data(result) == std_span_data(this) + {p1};
    ensures {p2} == {dynamic_extent} implies std_span_size(result) == std_span_size(this) - {p1};
    ensures {p2} != {dynamic_extent} implies std_span_size(result) == {p2};
}",
    },
];

// `std::span<T, N>` with static extent `N`: a view of `[data, data + N)`. The
// extent is the template argument, not state, so the contracts state it as
// the literal `{extent}`; only the data pointer is a model accessor. The
// subviews taking a runtime count return dynamic-extent spans.
const STATIC_SPAN_CATALOG: &[CatalogEntry] = &[
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::size",
        signature: "unsigned long (void) const noexcept",
        contract: "extern uint64 {name}(const struct {record}* this) {
    ensures result == {extent}u64;
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::size_bytes",
        signature: "unsigned long (void) const noexcept",
        contract: "extern uint64 {name}(const struct {record}* this) {
    ensures result == {extent_bytes}u64;
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::data",
        signature: "{T_signature} *(void) const noexcept",
        contract: "extern {element}* {name}(const struct {record}* this) {
    views std_span_data(this);
    ensures result == std_span_data(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::front",
        signature: "{T_signature} &(void) const noexcept",
        contract: "extern {element}& {name}(const struct {record}* this) {
    views std_span_data(this);
    requires 1u64 <= {extent}u64;
    ensures &result == std_span_data(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::back",
        signature: "{T_signature} &(void) const noexcept",
        contract: "extern {element}& {name}(const struct {record}* this) {
    views std_span_data(this);
    requires 1u64 <= {extent}u64;
    ensures &result == std_span_data(this) + ({extent}u64 - 1u64);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::operator[]",
        signature: "{T_signature} &(unsigned long) const noexcept",
        contract: "extern {element}& {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    requires {p1} < {extent}u64;
    ensures &result == std_span_data(this) + {p1};
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::first",
        signature: "class std::span<{T_signature}> (unsigned long) const noexcept",
        contract: "extern struct {result_record} {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    requires {p1} <= {extent}u64;
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == {p1};
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::last",
        signature: "class std::span<{T_signature}> (unsigned long) const noexcept",
        contract: "extern struct {result_record} {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    requires {p1} <= {extent}u64;
    ensures std_span_data(result) == std_span_data(this) + ({extent}u64 - {p1});
    ensures std_span_size(result) == {p1};
}",
    },
    CatalogEntry {
        qualified_name: "std::span<{T}, {N}>::subspan",
        signature: "class std::span<{T_signature}> (unsigned long, unsigned long) const noexcept",
        contract: "extern struct {result_record} {name}(const struct {record}* this, uint64 {p1}, uint64 {p2}) {
    views std_span_data(this);
    requires {p1} <= {extent}u64;
    requires {p2} != {dynamic_extent} implies {p2} <= {extent}u64 - {p1};
    ensures std_span_data(result) == std_span_data(this) + {p1};
    ensures {p2} == {dynamic_extent} implies std_span_size(result) == {extent}u64 - {p1};
    ensures {p2} != {dynamic_extent} implies std_span_size(result) == {p2};
}",
    },
];

// `std::array<T, N>`: `N` elements held in the object, `std_array_data(a)`.
// The element accessors have a const and a mutable overload; they require
// an index inside the array and form an address without reading it.
const ARRAY_CATALOG: &[CatalogEntry] = &[
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::size",
        signature: "unsigned long (void) const noexcept",
        contract: "extern uint64 {name}(const struct {record}* this) {
    ensures result == {extent}u64;
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::data",
        signature: "{T_signature} *(void) noexcept",
        contract: "extern {element}* {name}(struct {record}* this) {
    ensures result == &std_array_data(this)[0];
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::data",
        signature: "const {T_signature} *(void) const noexcept",
        contract: "extern const {element}* {name}(const struct {record}* this) {
    ensures result == &std_array_data(this)[0];
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::operator[]",
        signature: "{T_signature} &(unsigned long) noexcept",
        contract: "extern {element}& {name}(struct {record}* this, uint64 {p1}) {
    requires {p1} < {extent}u64;
    ensures &result == &std_array_data(this)[{p1}];
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::operator[]",
        signature: "const {T_signature} &(unsigned long) const noexcept",
        contract: "extern const {element}& {name}(const struct {record}* this, uint64 {p1}) {
    requires {p1} < {extent}u64;
    ensures &result == &std_array_data(this)[{p1}];
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::front",
        signature: "{T_signature} &(void) noexcept",
        contract: "extern {element}& {name}(struct {record}* this) {
    requires 1u64 <= {extent}u64;
    ensures &result == &std_array_data(this)[0];
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::front",
        signature: "const {T_signature} &(void) const noexcept",
        contract: "extern const {element}& {name}(const struct {record}* this) {
    requires 1u64 <= {extent}u64;
    ensures &result == &std_array_data(this)[0];
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::back",
        signature: "{T_signature} &(void) noexcept",
        contract: "extern {element}& {name}(struct {record}* this) {
    requires 1u64 <= {extent}u64;
    ensures &result == &std_array_data(this)[{extent}u64 - 1u64];
}",
    },
    CatalogEntry {
        qualified_name: "std::array<{T}, {N}>::back",
        signature: "const {T_signature} &(void) const noexcept",
        contract: "extern const {element}& {name}(const struct {record}* this) {
    requires 1u64 <= {extent}u64;
    ensures &result == &std_array_data(this)[{extent}u64 - 1u64];
}",
    },
];

// Entries for one instantiation, outside the generic span family.
const CATALOG: &[CatalogEntry] = &[CatalogEntry {
    qualified_name: "std::as_writable_bytes",
    signature: "class std::span<enum std::byte> (class std::span<int>) noexcept",
    contract: "extern struct {result_record} {name}(struct {argument_record} {p0}) {
    ensures std_span_data(result) == old((uint8*)std_span_data({p0}));
    ensures std_span_size(result) == old(std_span_size({p0})) * 4u64;
}",
}];

/// The catalog contract template for a standard function, with its span
/// element, if any, substituted.
pub(super) fn catalog_contract(axiom: &super::schema::CppAxiom) -> Option<String> {
    if let Some(entry) = CATALOG.iter().find(|entry| {
        entry.qualified_name == axiom.qualified_name && entry.signature == axiom.signature
    }) {
        return Some(entry.contract.to_string());
    }
    // The element, and a static extent if there is one, are the template
    // arguments the qualified name spells; an entry matches only when its
    // signature spells the same element.
    let (array, arguments) = if let Some(rest) = axiom.qualified_name.strip_prefix("std::span<") {
        (false, rest)
    } else {
        (true, axiom.qualified_name.strip_prefix("std::array<")?)
    };
    let arguments = arguments.rsplit_once(">::")?.0;
    let (element_name, extent) = match arguments.rsplit_once(", ") {
        Some((element, extent)) => (element, Some(extent.parse::<u64>().ok()?)),
        None => (arguments, None),
    };
    // An array's elements are its own objects; a const element type is
    // not one the catalog states.
    if array && (extent.is_none() || element_name.starts_with("const ")) {
        return None;
    }
    let element = SPAN_ELEMENTS
        .iter()
        .find(|element| element.name == element_name)?;
    // `std::dynamic_extent` is never spelled as a static extent.
    if extent.is_some_and(|extent| extent == u64::MAX) {
        return None;
    }
    let extent_text = extent.map(|extent| extent.to_string()).unwrap_or_default();
    let instantiate = |pattern: &str| {
        pattern
            .replace("{T_signature}", element.signature)
            .replace("{T}", element.name)
            .replace("{N}", &extent_text)
    };
    let family = if array {
        ARRAY_CATALOG
    } else if extent.is_some() {
        STATIC_SPAN_CATALOG
    } else {
        SPAN_CATALOG
    };
    let entry = family.iter().find(|entry| {
        instantiate(entry.qualified_name) == axiom.qualified_name
            && instantiate(entry.signature) == axiom.signature
    })?;
    let mut contract = entry
        .contract
        .replace("{element}", element.click)
        .replace("{bytes}", &element.bytes.to_string())
        .replace("{dynamic_extent}", DYNAMIC_EXTENT);
    if let Some(extent) = extent {
        // An extent whose byte size does not fit is not stated.
        let extent_bytes = extent.checked_mul(element.bytes)?;
        contract = contract
            .replace("{extent_bytes}", &extent_bytes.to_string())
            .replace("{extent}", &extent_text);
    }
    Some(contract)
}

/// The Click contracts for the axioms an import reaches, as `extern`
/// declarations. An axiom without a catalog entry gets none, so a caller
/// is refused unless the sidecar states one itself.
pub(super) fn contracts(
    import: &super::PreparedCppImport,
    names: &super::names::ResolvedNames,
) -> Result<String, String> {
    let mut source = String::new();
    for function in &import.export().reachable_functions {
        let Some(axiom) = &function.axiom else {
            continue;
        };
        if let Some(contract) = super::library_models::contract(
            import,
            function,
            names.require(&function.declaration_id)?,
        ) {
            source.push_str(&contract);
            source.push('\n');
            continue;
        }
        let Some(contract) = catalog_contract(axiom) else {
            continue;
        };
        let record = match &function.function_kind {
            super::CppFunctionKind::Method { record_name, .. } => record_name.as_str(),
            _ => "",
        };
        let mut contract = contract
            .replace("{name}", names.require(&function.declaration_id)?)
            .replace("{record}", record);
        if let super::CppType::Record { name, .. } = &function.return_type {
            contract = contract.replace("{result_record}", name);
        }
        if let Some(parameter) = function.parameters.first()
            && let super::CppType::Record { name, .. } = &parameter.value_type
        {
            contract = contract.replace("{argument_record}", name);
        }
        let receiver_count = usize::from(matches!(
            function.function_kind,
            super::CppFunctionKind::Method { .. }
        ));
        for (index, parameter) in function.parameters.iter().enumerate().skip(receiver_count) {
            contract = contract.replace(&format!("{{p{index}}}"), &parameter.name);
        }
        source.push_str(&contract);
        source.push('\n');
    }
    Ok(source)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::languages::c::syntax::{C0Type, LongRank};

    fn record(fields: &[(&str, C0Type, Option<&str>, u32, u32)]) -> C0StructLayout {
        C0StructLayout::from_explicit_fields_with_structs(
            fields
                .iter()
                .map(|(name, kind, nested, offset, width)| {
                    (
                        name.to_string(),
                        *kind,
                        nested.map(str::to_string),
                        *offset,
                        *width,
                    )
                })
                .collect(),
            16,
            8,
            &BTreeMap::from([(
                "__extent_storage".to_string(),
                C0StructLayout::from_explicit_fields(
                    vec![(
                        "_M_extent_value".to_string(),
                        C0Type::UInt64(LongRank::Long),
                        0,
                        8,
                    )],
                    8,
                    8,
                )
                .unwrap(),
            )]),
        )
        .unwrap()
    }

    fn accessors(span: C0StructLayout) -> BTreeMap<&'static str, &'static [&'static str]> {
        let mut layouts = BTreeMap::from([("span__unsigned_char".to_string(), span)]);
        layouts.insert(
            "__extent_storage".to_string(),
            C0StructLayout::from_explicit_fields(
                vec![(
                    "_M_extent_value".to_string(),
                    C0Type::UInt64(LongRank::Long),
                    0,
                    8,
                )],
                8,
                8,
            )
            .unwrap(),
        );
        model_accessors(&layouts)
    }

    #[test]
    fn libstdcxx_and_libcxx_span_layouts_bind_the_same_accessors() {
        let libstdcxx = accessors(record(&[
            ("_M_ptr", C0Type::UInt8Pointer, None, 0, 8),
            ("_M_extent", C0Type::Int32, Some("__extent_storage"), 8, 8),
        ]));
        assert_eq!(libstdcxx["std_span_data"], &["_M_ptr"]);
        assert_eq!(
            libstdcxx["std_span_size"],
            &["_M_extent", "_M_extent_value"]
        );
        let libcxx = accessors(record(&[
            ("__data_", C0Type::UInt8Pointer, None, 0, 8),
            ("__size_", C0Type::UInt64(LongRank::Long), None, 8, 8),
        ]));
        assert_eq!(libcxx["std_span_data"], &["__data_"]);
        assert_eq!(libcxx["std_span_size"], &["__size_"]);
    }

    #[test]
    fn an_unknown_or_ambiguous_span_layout_binds_no_accessor() {
        let unknown = accessors(record(&[
            ("pointer", C0Type::UInt8Pointer, None, 0, 8),
            ("length", C0Type::UInt64(LongRank::Long), None, 8, 8),
        ]));
        assert!(unknown.is_empty(), "{unknown:?}");
        let ambiguous = accessors(record(&[
            ("_M_ptr", C0Type::UInt8Pointer, None, 0, 8),
            ("__data_", C0Type::UInt8Pointer, None, 8, 8),
        ]));
        assert!(!ambiguous.contains_key("std_span_data"), "{ambiguous:?}");
    }

    #[test]
    fn span_entries_are_generic_over_supported_elements_only() {
        let axiom = |qualified_name: &str, signature: &str| super::super::schema::CppAxiom {
            declaration_header: None,
            qualified_name: qualified_name.into(),
            signature: signature.into(),
        };
        let bytes = catalog_contract(&axiom(
            "std::span<std::byte>::size_bytes",
            "unsigned long (void) const noexcept",
        ))
        .unwrap();
        assert!(bytes.contains("std_span_size(this) * 1u64"), "{bytes}");
        let data = catalog_contract(&axiom(
            "std::span<unsigned int>::data",
            "unsigned int *(void) const noexcept",
        ))
        .unwrap();
        assert!(data.starts_with("extern uint32* "), "{data}");
        // The signature must spell the same element as the name.
        assert!(
            catalog_contract(&axiom(
                "std::span<unsigned int>::data",
                "int *(void) const noexcept"
            ))
            .is_none()
        );
        // An element the catalog cannot state has no entry.
        assert!(
            catalog_contract(&axiom(
                "std::span<long>::size",
                "unsigned long (void) const noexcept"
            ))
            .is_none()
        );
    }
}
