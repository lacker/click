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
/// dynamic value is `_M_extent_value`.
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
];

/// The model accessors the parsed records support, each with its field path.
/// An accessor is available when some record of its template has the bound
/// path; a library whose layout does not match binds none.
pub(crate) fn model_accessors(
    layouts: &BTreeMap<String, C0StructLayout>,
) -> BTreeMap<&'static str, &'static [&'static str]> {
    let mut accessors = BTreeMap::new();
    for binding in BINDINGS {
        let bound = layouts.iter().any(|(name, layout)| {
            name.starts_with(binding.record_prefix) && has_path(layouts, layout, binding.path)
        });
        if bound {
            accessors.insert(binding.accessor, binding.path);
        }
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
struct CatalogEntry {
    qualified_name: &'static str,
    signature: &'static str,
    contract: &'static str,
}

// These catalog contracts are explicit library assumptions. Byte-view conversion
// states address/extent; it grants no backing authority or initialized values.
const AS_WRITABLE_BYTES_32_CONTRACT: &str =
    "extern struct {result_record} {name}(struct {argument_record} {p0}) {
    ensures std_span_data(result) == old((uint8*)std_span_data({p0}));
    ensures std_span_size(result) == old(std_span_size({p0})) * 4u64;
}
";

// `std::span<int>`: a view of `[data, data + size)`. The element accessors
// require an index inside the view, which the standard makes a
// precondition; they form an address and read nothing.
const CATALOG: &[CatalogEntry] = &[
    CatalogEntry {
        qualified_name: "std::as_writable_bytes",
        signature: "class std::span<enum std::byte> (class std::span<int>) noexcept",
        contract: AS_WRITABLE_BYTES_32_CONTRACT,
    },
    CatalogEntry {
        qualified_name: "std::as_writable_bytes",
        signature: "class std::span<enum std::byte> (class std::span<unsigned int>) noexcept",
        contract: AS_WRITABLE_BYTES_32_CONTRACT,
    },
    CatalogEntry {
        qualified_name: "std::span<std::byte>::data",
        signature: "enum std::byte *(void) const noexcept",
        contract: "extern uint8* {name}(const struct {record}* this) {
    views std_span_data(this);
    ensures result == std_span_data(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<int>::size",
        signature: "unsigned long (void) const noexcept",
        contract: "extern uint64 {name}(const struct {record}* this) {
    views std_span_size(this);
    ensures result == std_span_size(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<int>::data",
        signature: "int *(void) const noexcept",
        contract: "extern int32* {name}(const struct {record}* this) {
    views std_span_data(this);
    ensures result == std_span_data(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<int>::front",
        signature: "int &(void) const noexcept",
        contract: "extern int32& {name}(const struct {record}* this) {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<int>::back",
        signature: "int &(void) const noexcept",
        contract: "extern int32& {name}(const struct {record}* this) {
    views std_span_data(this);
    views std_span_size(this);
    requires 1u64 <= std_span_size(this);
    ensures &result == std_span_data(this) + (std_span_size(this) - 1u64);
}",
    },
    CatalogEntry {
        qualified_name: "std::span<int>::operator[]",
        signature: "int &(unsigned long) const noexcept",
        contract: "extern int32& {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    views std_span_size(this);
    requires {p1} < std_span_size(this);
    ensures &result == std_span_data(this) + {p1};
}",
    },
    CatalogEntry {
        qualified_name: "std::span<int>::first",
        signature: "class std::span<int> (unsigned long) const noexcept",
        contract: "extern struct {record} {name}(const struct {record}* this, uint64 {p1}) {
    views std_span_data(this);
    views std_span_size(this);
    requires {p1} <= std_span_size(this);
    ensures std_span_data(result) == std_span_data(this);
    ensures std_span_size(result) == {p1};
}",
    },
];

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
        let Some(entry) = CATALOG.iter().find(|entry| {
            entry.qualified_name == axiom.qualified_name && entry.signature == axiom.signature
        }) else {
            continue;
        };
        let record = match &function.function_kind {
            super::CppFunctionKind::Method { record_name, .. } => record_name.as_str(),
            _ => "",
        };
        let mut contract = entry
            .contract
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
