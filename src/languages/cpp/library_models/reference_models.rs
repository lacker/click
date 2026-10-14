//! Checked, non-reading reference getters for exact pinned library declarations.
use super::*;
use crate::languages::cpp::scalar::{Scalar, ScalarKind};

#[derive(Clone, Copy)]
enum Getter {
    Index,
    Front,
    Back,
}

pub(super) struct ReferenceModel<'a> {
    record: &'a super::super::schema::CppRecord,
    scalar: Scalar,
    getter: Getter,
    array: bool,
    extent: Option<u64>,
    data: Vec<&'a str>,
    size: Vec<&'a str>,
    header: &'static str,
    digest: &'static str,
}

pub(super) fn selected<'a>(
    import: &'a PreparedCppImport,
    source: &CppFunction,
) -> Option<ReferenceModel<'a>> {
    let axiom = source.axiom.as_ref()?;
    super::super::standard_library::catalog_contract(axiom)?;
    let (class, method) = axiom.qualified_name.rsplit_once("::")?;
    let array = class.starts_with("std::array<");
    if !array && !class.starts_with("std::span<") {
        return None;
    }
    let getter = match method {
        "operator[]" => Getter::Index,
        "front" => Getter::Front,
        "back" => Getter::Back,
        _ => return None,
    };
    let (header, digest, data_name, size_path) = match axiom.declaration_header.as_deref()? {
        "sysroot/usr/include/c++/12/span" if !array => (
            SPAN_HEADER,
            SPAN_SHA256,
            "_M_ptr",
            vec!["_M_extent", "_M_extent_value"],
        ),
        "sysroot/usr/include/c++/12/array" if array => (
            "sysroot/usr/include/c++/12/array",
            "05205589a4c5619b434b3e197c6677b4cf3553ca002b48bc607a1b0e860921ce",
            "_M_elems",
            vec![],
        ),
        "libcxx/include/c++/v1/span" if !array => (
            "libcxx/include/c++/v1/span",
            "b8b350b8a4992602c184694bee10ac1dc4a7e9412a02988c9e6466972195ba10",
            "__data_",
            vec!["__size_"],
        ),
        _ => return None,
    };
    if import.dependency_digest(header) != Some(digest) || !source.declared_noexcept {
        return None;
    }
    let CppFunctionKind::Method {
        record_declaration_id,
        is_const,
        ..
    } = &source.function_kind
    else {
        return None;
    };
    if !receiver_matches(source, record_declaration_id, *is_const)
        || source.parameters.len()
            != if matches!(getter, Getter::Index) {
                2
            } else {
                1
            }
    {
        return None;
    }
    if matches!(getter, Getter::Index)
        && !Scalar::is(&source.parameters[1].value_type, ScalarKind::UInt64, false)
    {
        return None;
    }
    let suffix = format!(
        "@F@{method}{}#{}",
        if matches!(getter, Getter::Index) {
            "#l"
        } else {
            ""
        },
        if *is_const { "1" } else { "" }
    );
    if source.declaration_id != format!("{record_declaration_id}{suffix}") {
        return None;
    }
    let CppType::LvalueReference { pointee } = &source.return_type else {
        return None;
    };
    let scalar = Scalar::of(pointee)?;
    if !matches!(
        scalar.kind,
        ScalarKind::Int32 | ScalarKind::UInt32 | ScalarKind::UInt8
    ) {
        return None;
    }
    let record = import
        .export()
        .records
        .iter()
        .find(|record| &record.declaration_id == record_declaration_id)?;
    if record.span.file != header || record.base.is_some() {
        return None;
    }
    let data = record.fields.iter().find(|field| field.name == data_name)?;
    if data.offset_bytes != 0
        || data.declaration_id != format!("{record_declaration_id}@FI@{data_name}")
    {
        return None;
    }
    let arguments = class.strip_suffix('>')?.split_once('<')?.1;
    let extent = match arguments.rsplit_once(", ") {
        Some((_, extent)) => Some(extent.parse::<u64>().ok()?),
        None => None,
    };
    let element_name = arguments.split(", ").next()?;
    let (element_id, expected_kind, element_const) = match element_name {
        "int" => ("I", ScalarKind::Int32, false),
        "const int" => ("1I", ScalarKind::Int32, true),
        "unsigned int" => ("i", ScalarKind::UInt32, false),
        "const unsigned int" => ("1i", ScalarKind::UInt32, true),
        "unsigned char" => ("c", ScalarKind::UInt8, false),
        "const unsigned char" => ("1c", ScalarKind::UInt8, true),
        "std::byte" => ("$@N@std@E@byte", ScalarKind::UInt8, false),
        "const std::byte" => ("1$@N@std@E@byte", ScalarKind::UInt8, true),
        _ => return None,
    };
    let namespace = if header.starts_with("libcxx/") {
        "c:@N@std@N@__1"
    } else {
        "c:@N@std"
    };
    let template = if array { "array" } else { "span" };
    let expected_record = format!(
        "{namespace}@S@{template}>#{element_id}#Vl{}",
        extent.unwrap_or(u64::MAX)
    );
    if *record_declaration_id != expected_record
        || scalar.kind != expected_kind
        || (!array && scalar.is_const != element_const)
    {
        return None;
    }
    let ty = scalar.kind.kernel_type();
    if array {
        let CppType::Array { element, length } = &data.value_type else {
            return None;
        };
        if Scalar::mutable_kind(element) != Some(scalar.kind)
            || extent != Some(u64::from(*length))
            || *length == 0
            || scalar.is_const != *is_const
            || record.fields.len() != 1
            || record.size_bytes != length.checked_mul(ty.byte_width())?
            || record.alignment_bytes != ty.byte_width()
        {
            return None;
        }
    } else {
        let CppType::Pointer { pointee: element } = &data.value_type else {
            return None;
        };
        if Scalar::of(element) != Some(scalar)
            || data.size_bytes != 8
            || record.alignment_bytes != 8
        {
            return None;
        }
        let expected_fields = if extent.is_some() { 1 } else { 2 };
        if record.fields.len() != expected_fields
            || record.size_bytes != if extent.is_some() { 8 } else { 16 }
        {
            return None;
        }
        if extent.is_none() {
            let size = record
                .fields
                .iter()
                .find(|field| field.name == size_path[0])?;
            if size.offset_bytes != 8
                || size.size_bytes != 8
                || size.declaration_id != format!("{record_declaration_id}@FI@{}", size_path[0])
            {
                return None;
            }
            if size_path.len() == 1 {
                if !Scalar::is(&size.value_type, ScalarKind::UInt64, false) {
                    return None;
                }
            } else {
                let inner = import.export().records.iter().find(|record| {
                    Some(record.declaration_id.as_str()) == record_id(&size.value_type)
                })?;
                if inner.span.file != header
                    || inner.size_bytes != 8
                    || inner.alignment_bytes != 8
                    || inner.fields.len() != 1
                    || inner.fields[0].name != size_path[1]
                    || inner.fields[0].offset_bytes != 0
                    || !Scalar::is(&inner.fields[0].value_type, ScalarKind::UInt64, false)
                {
                    return None;
                }
            }
        }
    }
    Some(ReferenceModel {
        record,
        scalar,
        getter,
        array,
        extent,
        data: vec![data_name],
        size: size_path,
        header,
        digest,
    })
}

impl ReferenceModel<'_> {
    fn index(&self, source: &CppFunction) -> String {
        match self.getter {
            Getter::Index => source.parameters[1].name.clone(),
            Getter::Front => "0u64".into(),
            Getter::Back => format!(
                "({} - 1u64)",
                self.extent.map_or_else(
                    || "std_span_size(this)".into(),
                    |extent| format!("{extent}u64")
                )
            ),
        }
    }
    pub(super) fn assumption(&self, source: &CppFunction) -> String {
        format!(
            "assumed source-to-model equivalence for {} [{} SHA256 {}]; non-reading reference implementation requires independent checked certification",
            source.axiom.as_ref().unwrap().qualified_name,
            self.header,
            self.digest
        )
    }
    pub(super) fn contract(&self, source: &CppFunction, name: &str) -> Option<String> {
        let mut contract =
            super::super::standard_library::catalog_contract(source.axiom.as_ref()?)?
                .replacen("extern ", "", 1)
                .replace("{name}", name)
                .replace("{record}", &self.record.name);
        for (index, parameter) in source.parameters.iter().enumerate().skip(1) {
            contract = contract.replace(&format!("{{p{index}}}"), &parameter.name);
        }
        if self.array {
            contract = contract.replacen(
                "    ensures",
                "    requires valid_place(this);\n    ensures",
                1,
            );
        } else {
            let bound = match self.getter {
                Getter::Index => format!("({} + 1u64)", self.index(source)),
                Getter::Front => "1u64".into(),
                Getter::Back => self.extent.map_or_else(
                    || "std_span_size(this)".into(),
                    |extent| format!("{extent}u64"),
                ),
            };
            contract = contract.replacen(
                "    ensures",
                &format!("    requires valid_place(std_span_data(this)[0..{bound}]);\n    ensures"),
                1,
            );
        }
        let proof = if !self.array && matches!(self.getter, Getter::Index) {
            let index = self.index(source);
            // idx < size already excludes UINT64_MAX. Name that consequence
            // explicitly so the checked model can cite ordinary numeric laws.
            contract = contract.replacen(
                "    ensures",
                &format!("    requires {index} < 18446744073709551615u64;\n    ensures"),
                1,
            );
            format!(
                "apply(uint64_less_than_to_integer({index}, 18446744073709551615u64)) using {{ {index} < 18446744073709551615u64; }}\n have to_integer({index}) + 1 <= 18446744073709551615 by {{ arithmetic() using {{ to_integer({index}) < 18446744073709551615; }} }}\n apply(uint64_add_to_integer({index}, 1u64)) using {{ to_integer({index}) + 1 <= 18446744073709551615; }}\n have to_integer({index}) < to_integer({index} + 1u64) by {{ arithmetic() using {{ to_integer({index} + 1u64) == to_integer({index}) + to_integer(1u64); }} }}\n apply(uint64_to_integer_less_than_implies_less_than({index}, {index} + 1u64)) using {{ to_integer({index}) < to_integer({index} + 1u64); }}\n execute(); simp();"
            )
        } else {
            "execute(); simp();".into()
        };
        Some(format!("{contract} by {{ {proof} }}\n"))
    }
    pub(super) fn implementation(
        &self,
        source: &CppFunction,
        function: CFunction,
        layouts: &BTreeMap<String, Arc<CAggregateLayout>>,
    ) -> Result<CFunction, String> {
        let layout = layouts
            .get(&self.record.name)
            .ok_or("reference model record layout missing")?
            .clone();
        let ty = self.scalar.kind.kernel_type();
        let mut data = if self.array {
            let length = u32::try_from(self.extent.ok_or("array model extent missing")?)
                .map_err(|_| "array model extent unsupported")?;
            let array_type = match ty {
                CType::Int32 => CType::Int32Array(length),
                CType::UInt32 => CType::UInt32Array(length),
                CType::UInt8 => CType::UInt8Array(length),
                _ => return Err("reference model element unsupported".into()),
            };
            c_typed_load(
                member(layout.clone(), c_variable("this"), &self.data, array_type),
                array_type,
            )
        } else {
            let pointer_type = self
                .scalar
                .kind
                .pointer_kernel_type()
                .ok_or("reference model pointer type unsupported")?;
            c_typed_load(
                member(layout.clone(), c_variable("this"), &self.data, pointer_type),
                pointer_type,
            )
        };
        if let CExpression::TypedLoad {
            pointee_constant, ..
        } = &mut data
        {
            *pointee_constant = self.scalar.is_const;
        }
        let index = match self.getter {
            Getter::Index => c_variable(&source.parameters[1].name),
            Getter::Front => c_uint64_literal(0),
            Getter::Back => c_subtract(
                self.extent.map_or_else(
                    || {
                        c_typed_load(
                            member(layout, c_variable("this"), &self.size, CType::UInt64),
                            CType::UInt64,
                        )
                    },
                    c_uint64_literal,
                ),
                c_uint64_literal(1),
            ),
        };
        Ok(
            function.with_body(c_return(c_checked_object_address(c_typed_load(
                c_add(data, index),
                ty,
            )))),
        )
    }
}
