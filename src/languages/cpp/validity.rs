//! Recursive artifact metadata validity, independent of the supported semantic profile.
//!
//! This pass borrows the syntax tree. It never resolves places, builds lexical
//! environments, or decides which lifetime combinations or integer widths Click
//! supports. Local semantic validators reuse the metadata helpers for isolated
//! validation; the function entry checks every node before profile rejection.

use super::schema::*;
use std::collections::BTreeSet;

impl CppType {
    pub(super) fn validate_aliases_in(&self, sources: &BTreeSet<String>) -> Result<(), String> {
        self.check_aliases(&|file| sources.contains(file))
    }

    fn check_aliases(&self, accepts_source: &impl Fn(&str) -> bool) -> Result<(), String> {
        crate::instrumentation::record_deterministic_work(1);
        match self {
            Self::Enumeration {
                declaration_id,
                name,
                underlying_type,
                is_scoped,
                is_fixed,
                span,
                ..
            } => {
                identity(declaration_id, name, "enum")?;
                span.check_source(accepts_source(&span.file))?;
                if !is_scoped
                    || !is_fixed
                    || !matches!(
                        underlying_type.as_ref(),
                        CppType::Integer {
                            bits: 8,
                            signed: false,
                            is_const: false,
                            ..
                        }
                    )
                {
                    return Err(
                        "C++ enum requires a scoped declaration with fixed unsigned-byte backing"
                            .into(),
                    );
                }
                underlying_type.check_aliases(accepts_source)
            }
            Self::Integer { source_aliases, .. } => {
                let mut identities = BTreeSet::new();
                for alias in source_aliases {
                    crate::instrumentation::record_deterministic_work(1);
                    if alias.declaration_id.is_empty() || alias.name.is_empty() {
                        return Err("C++ integer type alias is missing declaration identity".into());
                    }
                    if !identities.insert(alias.declaration_id.as_str()) {
                        return Err("C++ integer type alias chain contains a cycle".into());
                    }
                    alias.span.check_source(accepts_source(&alias.span.file))?;
                }
                Ok(())
            }
            Self::LvalueReference { pointee } | Self::Pointer { pointee } => {
                pointee.check_aliases(accepts_source)
            }
            Self::Void | Self::Boolean { .. } | Self::Record { .. } => Ok(()),
        }
    }
}

impl CppSpan {
    pub(super) fn validate_in(&self, sources: &BTreeSet<String>) -> Result<(), String> {
        self.check_source(sources.contains(&self.file))
    }

    pub(super) fn validate(&self, logical_source: &str) -> Result<(), String> {
        self.check_source(self.file == logical_source)
    }

    fn check_source(&self, accepted: bool) -> Result<(), String> {
        if !accepted
            || self.start_line == 0
            || self.start_column == 0
            || self.end_line == 0
            || self.end_column == 0
            || (self.end_line, self.end_column) < (self.start_line, self.start_column)
        {
            return Err(format!("invalid C++ source span in `{}`", self.file));
        }
        Ok(())
    }
}

pub(super) fn check_function(
    function: &CppFunction,
    logical_source: &str,
    alias_sources: &BTreeSet<String>,
) -> Result<(), String> {
    check_function_with_types(function, logical_source, alias_sources, &|_| Ok(()))
}

pub(super) fn check_function_with_types(
    function: &CppFunction,
    logical_source: &str,
    alias_sources: &BTreeSet<String>,
    type_check: &dyn Fn(&CppType) -> Result<(), String>,
) -> Result<(), String> {
    let checker = Metadata {
        logical_source,
        alias_sources,
        type_check,
    };
    identity(&function.declaration_id, &function.name, "function")?;
    function.span.validate(logical_source)?;
    checker.value_type(&function.return_type)?;
    match &function.function_kind {
        CppFunctionKind::Free => {}
        CppFunctionKind::StaticMethod {
            record_declaration_id,
            record_name,
        }
        | CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        }
        | CppFunctionKind::Destructor {
            record_declaration_id,
            record_name,
        }
        | CppFunctionKind::Method {
            record_declaration_id,
            record_name,
            ..
        } => {
            if record_declaration_id.is_empty() || record_name.is_empty() {
                return Err("C++ function has a missing record/class identity".into());
            }
        }
    }
    for parameter in &function.parameters {
        checker.place(parameter)?;
    }
    checker.body(&function.body)
}

fn identity(id: &str, name: &str, label: &str) -> Result<(), String> {
    if id.is_empty() || name.is_empty() {
        return Err(format!("C++ {label} is missing declaration identity"));
    }
    Ok(())
}

struct Metadata<'a> {
    logical_source: &'a str,
    alias_sources: &'a BTreeSet<String>,
    type_check: &'a dyn Fn(&CppType) -> Result<(), String>,
}

impl Metadata<'_> {
    fn value_type(&self, value: &CppType) -> Result<(), String> {
        value.validate_aliases_in(self.alias_sources)?;
        (self.type_check)(value)
    }

    fn place(&self, place: &CppPlace) -> Result<(), String> {
        identity(&place.declaration_id, &place.name, "place")?;
        place.span.validate(self.logical_source)?;
        self.value_type(&place.value_type)
    }

    fn reference(&self, place: &CppPlaceReference) -> Result<(), String> {
        identity(&place.declaration_id, &place.name, "place reference")?;
        super::budget::limit(
            "record field projections",
            place.projections.len(),
            super::budget::MAX_RECORDS,
        )?;
        for projection in &place.projections {
            match projection {
                CppProjection::Field(field) => self.field(field)?,
                CppProjection::Base { base } => {
                    identity(&base.base_declaration_id, &base.base_name, "base reference")?;
                    if base.record_declaration_id.is_empty() {
                        return Err("C++ base reference is missing derived record identity".into());
                    }
                    base.span.validate(self.logical_source)?;
                }
            }
        }
        place.span.validate(self.logical_source)
    }

    fn callee(&self, callee: &CppFunctionReference) -> Result<(), String> {
        identity(&callee.declaration_id, &callee.name, "call")?;
        callee.span.validate(self.logical_source)
    }

    fn field(&self, field: &CppFieldReference) -> Result<(), String> {
        identity(&field.declaration_id, &field.name, "field reference")?;
        if field.record_declaration_id.is_empty() {
            return Err("C++ field reference is missing record declaration identity".into());
        }
        field.span.validate(self.logical_source)
    }

    fn expression(&self, expression: &CppExpression) -> Result<(), String> {
        crate::instrumentation::record_deterministic_work(1);
        self.value_type(expression.value_type())?;
        let span = match expression {
            CppExpression::ObserverCall {
                callee,
                arguments,
                span,
                ..
            } => {
                self.callee(callee)?;
                self.arguments(arguments)?;
                span
            }
            CppExpression::RuntimeConstantEvaluation { span, .. }
            | CppExpression::IntegerLiteral { span, .. }
            | CppExpression::NullPointer { span, .. }
            | CppExpression::CompilerConstant { span, .. } => span,
            CppExpression::ConstantReference { constant, span, .. } => {
                identity(
                    &constant.declaration_id,
                    &constant.name,
                    "constant reference",
                )?;
                constant.span.validate(self.logical_source)?;
                span
            }
            CppExpression::Load { place, span, .. }
            | CppExpression::AddressOf { place, span, .. } => {
                self.reference(place)?;
                span
            }
            CppExpression::Dereference { pointer, span, .. }
            | CppExpression::ReferenceBinding {
                address: pointer,
                span,
                ..
            } => {
                self.expression(pointer)?;
                span
            }
            CppExpression::MemberLoad {
                object,
                field,
                span,
                ..
            } => {
                self.reference(object)?;
                self.field(field)?;
                span
            }
            CppExpression::LogicalNot { value, span, .. }
            | CppExpression::IntegralCast { value, span, .. }
            | CppExpression::EnumCast { value, span, .. }
            | CppExpression::BytePointerCast { value, span, .. } => {
                self.expression(value)?;
                span
            }
            CppExpression::Binary {
                left, right, span, ..
            } => {
                self.expression(left)?;
                self.expression(right)?;
                span
            }
        };
        span.validate(self.logical_source)
    }

    fn arguments(&self, arguments: &[CppCallArgument]) -> Result<(), String> {
        for argument in arguments {
            crate::instrumentation::record_deterministic_work(1);
            match argument {
                CppCallArgument::Value { value } => self.expression(value)?,
                CppCallArgument::Reference { place } => self.reference(place)?,
                CppCallArgument::RecordCopy {
                    place,
                    value_type,
                    span,
                } => {
                    self.reference(place)?;
                    self.value_type(value_type)?;
                    span.validate(self.logical_source)?;
                }
                CppCallArgument::Call {
                    callee,
                    arguments,
                    value_type,
                    span,
                }
                | CppCallArgument::RecordConstruct {
                    callee,
                    arguments,
                    value_type,
                    span,
                } => {
                    self.callee(callee)?;
                    self.value_type(value_type)?;
                    span.validate(self.logical_source)?;
                    self.arguments(arguments)?;
                }
            }
        }
        Ok(())
    }

    fn conversions(&self, conversions: &[super::CppScalarConversion]) -> Result<(), String> {
        for conversion in conversions {
            crate::instrumentation::record_deterministic_work(1);
            conversion.span.validate(self.logical_source)?;
            self.value_type(&conversion.source_type)?;
            self.value_type(&conversion.value_type)?;
        }
        Ok(())
    }

    fn initializer(&self, initializer: &CppInitializer) -> Result<(), String> {
        match initializer {
            CppInitializer::Uninitialized => Ok(()),
            CppInitializer::Value { value } => self.expression(value),
            CppInitializer::Call {
                callee,
                arguments,
                conversions,
                span,
            } => {
                span.validate(self.logical_source)?;
                self.callee(callee)?;
                self.arguments(arguments)?;
                self.conversions(conversions)?;
                Ok(())
            }
            CppInitializer::ConstructionCall {
                callee,
                arguments,
                span,
            }
            | CppInitializer::Constructor {
                callee,
                arguments,
                span,
            } => {
                span.validate(self.logical_source)?;
                self.callee(callee)?;
                self.arguments(arguments)
            }
            CppInitializer::Aggregate { fields, span } => {
                span.validate(self.logical_source)?;
                for initializer in fields {
                    crate::instrumentation::record_deterministic_work(1);
                    initializer.span.validate(self.logical_source)?;
                    self.field(&initializer.field)?;
                    self.expression(&initializer.value)?;
                }
                Ok(())
            }
        }
    }

    fn cleanups(&self, cleanups: &[CppCleanup]) -> Result<(), String> {
        for cleanup in cleanups {
            crate::instrumentation::record_deterministic_work(1);
            match cleanup {
                CppCleanup::Destructor {
                    object,
                    callee,
                    span,
                } => {
                    self.reference(object)?;
                    self.callee(callee)?;
                    span.validate(self.logical_source)?;
                }
            }
        }
        Ok(())
    }

    fn body(&self, body: &[CppStatement]) -> Result<(), String> {
        for statement in body {
            crate::instrumentation::record_deterministic_work(1);
            let span = match statement {
                CppStatement::AssignConstructionCall {
                    target,
                    callee,
                    arguments,
                    value_type,
                    span,
                } => {
                    self.reference(target)?;
                    self.callee(callee)?;
                    self.arguments(arguments)?;
                    self.value_type(value_type)?;
                    span
                }
                CppStatement::TrivialCopy {
                    target,
                    source,
                    span,
                } => {
                    self.reference(target)?;
                    self.reference(source)?;
                    span
                }
                CppStatement::Declare {
                    local,
                    initializer,
                    span,
                } => {
                    self.place(local)?;
                    self.initializer(initializer)?;
                    span
                }
                CppStatement::Assign {
                    target,
                    value,
                    span,
                } => {
                    self.reference(target)?;
                    self.expression(value)?;
                    span
                }
                CppStatement::Store {
                    pointer,
                    value,
                    span,
                } => {
                    self.expression(pointer)?;
                    self.expression(value)?;
                    span
                }
                CppStatement::MemberConstruct {
                    object,
                    field,
                    callee,
                    arguments,
                    span,
                } => {
                    self.reference(object)?;
                    self.field(field)?;
                    self.callee(callee)?;
                    self.arguments(arguments)?;
                    span
                }
                CppStatement::MemberStore {
                    object,
                    field,
                    value,
                    span,
                } => {
                    self.reference(object)?;
                    self.field(field)?;
                    self.expression(value)?;
                    span
                }
                CppStatement::ReturnConstruct {
                    callee,
                    arguments,
                    value_type,
                    cleanups,
                    span,
                }
                | CppStatement::ReturnAggregateCall {
                    callee,
                    arguments,
                    value_type,
                    cleanups,
                    span,
                } => {
                    self.callee(callee)?;
                    self.arguments(arguments)?;
                    self.value_type(value_type)?;
                    self.cleanups(cleanups)?;
                    span
                }
                CppStatement::ReturnRecord {
                    source,
                    value_type,
                    cleanups,
                    span,
                } => {
                    self.reference(source)?;
                    self.value_type(value_type)?;
                    self.cleanups(cleanups)?;
                    span
                }
                CppStatement::Return {
                    value,
                    cleanups,
                    span,
                } => {
                    self.expression(value)?;
                    self.cleanups(cleanups)?;
                    span
                }
                CppStatement::Unreachable { span } => span,
                CppStatement::Throw { value, span }
                | CppStatement::Assume {
                    condition: value,
                    span,
                } => {
                    self.expression(value)?;
                    span
                }
                CppStatement::LibraryAssert {
                    condition,
                    contract,
                    metadata,
                    specialization,
                    span,
                } => {
                    super::schema::validate_library_assertion_metadata(
                        contract,
                        metadata,
                        specialization,
                    )?;
                    self.expression(condition)?;
                    span
                }
                CppStatement::ReturnCall {
                    callee,
                    arguments,
                    value_type,
                    conversions,
                    cleanups,
                    span,
                } => {
                    self.callee(callee)?;
                    self.arguments(arguments)?;
                    self.value_type(value_type)?;
                    self.conversions(conversions)?;
                    self.cleanups(cleanups)?;
                    span
                }
                CppStatement::Call {
                    callee,
                    arguments,
                    span,
                } => {
                    self.callee(callee)?;
                    self.arguments(arguments)?;
                    span
                }
                CppStatement::Scope {
                    body,
                    cleanups,
                    span,
                } => {
                    self.body(body)?;
                    self.cleanups(cleanups)?;
                    span
                }
                CppStatement::TryCatchInt32 {
                    try_body,
                    binding,
                    handler,
                    span,
                } => {
                    self.body(try_body)?;
                    self.place(binding)?;
                    self.body(handler)?;
                    span
                }
                CppStatement::If {
                    condition,
                    then_branch,
                    else_branch,
                    span,
                } => {
                    match condition {
                        CppCondition::Expression(value) => self.expression(value)?,
                        CppCondition::Call { call } => {
                            self.callee(&call.callee)?;
                            self.arguments(&call.arguments)?;
                            self.value_type(&call.value_type)?;
                            call.span.validate(self.logical_source)?;
                        }
                    }
                    self.body(then_branch)?;
                    self.body(else_branch)?;
                    span
                }
            };
            span.validate(self.logical_source)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};

    fn span() -> Value {
        json!({"file":"fixture.cpp","start_line":1,"start_column":1,"end_line":1,"end_column":2})
    }

    fn ty() -> Value {
        // A well-formed width outside the semantic profile is still valid metadata.
        json!({"kind":"integer","bits":16,"signed":true,"is_const":false,"source_aliases":[
            {"declaration_id":"alias","name":"Word","span":span()}
        ]})
    }

    fn reference() -> Value {
        json!({"declaration_id":"id","name":"name","span":span()})
    }

    fn field() -> Value {
        json!({"record_declaration_id":"record","declaration_id":"field","name":"value","span":span()})
    }

    fn literal() -> Value {
        json!({"kind":"integer_literal","value":"0","value_type":ty(),"span":span()})
    }

    fn place() -> Value {
        json!({"declaration_id":"local","name":"local","value_type":ty(),"span":span()})
    }

    fn cleanup() -> Value {
        json!({"kind":"destructor","object":reference(),"callee":reference(),"span":span()})
    }

    fn call_arguments() -> Value {
        json!([
            {"kind":"value","value":literal()},
            {"kind":"reference","place":reference()},
            {"kind":"call","callee":reference(),"arguments":[{"kind":"value","value":literal()}],"value_type":ty(),"span":span()}
        ])
    }

    fn fixture(body: Value) -> CppFunction {
        serde_json::from_value(json!({"declaration_id":"root","name":"root","function_kind":{"kind":"free"},
            "return_type":ty(),"parameters":[place()],"declared_noexcept":true,"span":span(),"body":body})).unwrap()
    }

    fn corpus() -> CppFunction {
        let mut body = vec![];
        for expression in [
            literal(),
            json!({"kind":"compiler_constant","value":"1","value_type":ty(),"span":span()}),
            json!({"kind":"constant_reference","constant":reference(),"value_type":ty(),"span":span()}),
            json!({"kind":"load","place":reference(),"value_type":ty(),"span":span()}),
            json!({"kind":"address_of","place":reference(),"value_type":{"kind":"pointer","pointee":ty()},"span":span()}),
            json!({"kind":"dereference","pointer":literal(),"value_type":ty(),"span":span()}),
            json!({"kind":"member_load","object":reference(),"field":field(),"value_type":ty(),"span":span()}),
            json!({"kind":"integral_cast","value":literal(),"value_type":ty(),"span":span()}),
            json!({"kind":"binary","operator":"add","left":literal(),"right":literal(),"value_type":ty(),"span":span()}),
            json!({"kind":"observer_call","callee":reference(),"arguments":call_arguments(),"value_type":ty(),"span":span()}),
        ] {
            body.push(
                json!({"kind":"return","value":expression,"cleanups":[cleanup()],"span":span()}),
            );
        }
        for initializer in [
            json!({"kind":"value","value":literal()}),
            json!({"kind":"call","callee":reference(),"arguments":call_arguments(),"span":span()}),
            json!({"kind":"constructor","callee":reference(),"arguments":call_arguments(),"span":span()}),
            json!({"kind":"aggregate","fields":[{"field":field(),"value":literal(),"span":span()}],"span":span()}),
        ] {
            body.push(
                json!({"kind":"declare","local":place(),"initializer":initializer,"span":span()}),
            );
        }
        body.extend([
            json!({"kind":"assign","target":reference(),"value":literal(),"span":span()}),
            json!({"kind":"store","pointer":literal(),"value":literal(),"span":span()}),
            json!({"kind":"member_store","object":reference(),"field":field(),"value":literal(),"span":span()}),
            json!({"kind":"return_call","callee":reference(),"arguments":call_arguments(),"value_type":ty(),"cleanups":[cleanup()],"span":span()}),
            json!({"kind":"call","callee":reference(),"arguments":call_arguments(),"span":span()}),
            json!({"kind":"throw","value":literal(),"span":span()}),
            json!({"kind":"assume","condition":literal(),"span":span()}),
        ]);
        // The same metadata is valid inside unsupported deeper arrangements.
        fixture(json!([{"kind":"if","condition":literal(),"then_branch":[
            {"kind":"scope","body":[{"kind":"try_catch_int32","try_body":body,"binding":place(),"handler":body,"span":span()}],"cleanups":[cleanup()],"span":span()}
        ],"else_branch":body,"span":span()}]))
    }

    fn span_paths(value: &Value, prefix: &str, result: &mut Vec<String>) {
        match value {
            Value::Object(fields) => {
                if fields.contains_key("start_line") {
                    result.push(prefix.to_string());
                }
                for (key, child) in fields {
                    span_paths(child, &format!("{prefix}/{key}"), result);
                }
            }
            Value::Array(elements) => {
                for (index, child) in elements.iter().enumerate() {
                    span_paths(child, &format!("{prefix}/{index}"), result);
                }
            }
            _ => {}
        }
    }

    #[test]
    fn metadata_covers_every_recursive_variant_before_profile_selection() {
        let function = corpus();
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        check_function(&function, "fixture.cpp", &sources).unwrap();
        let encoded = serde_json::to_value(&function).unwrap();
        let mut paths = vec![];
        span_paths(&encoded, "", &mut paths);
        assert!(paths.len() > 200);
        for path in paths {
            let mut forged = encoded.clone();
            forged
                .pointer_mut(&format!("{path}/start_line"))
                .map(|line| *line = json!(0))
                .unwrap();
            let function = serde_json::from_value(forged).unwrap();
            assert!(
                check_function(&function, "fixture.cpp", &sources)
                    .unwrap_err()
                    .contains("invalid C++ source span"),
                "missed {path}"
            );
        }
    }

    #[test]
    #[ignore = "nightly: 2s in the parallel gate"]
    fn metadata_rejects_missing_identities_in_nested_payloads() {
        fn identity_paths(value: &Value, prefix: &str, result: &mut Vec<String>) {
            match value {
                Value::Object(fields) => {
                    for (key, child) in fields {
                        let path = format!("{prefix}/{key}");
                        if matches!(
                            key.as_str(),
                            "declaration_id" | "record_declaration_id" | "name"
                        ) {
                            result.push(path);
                        } else {
                            identity_paths(child, &path, result);
                        }
                    }
                }
                Value::Array(elements) => {
                    for (index, child) in elements.iter().enumerate() {
                        identity_paths(child, &format!("{prefix}/{index}"), result);
                    }
                }
                _ => {}
            }
        }
        let sources = BTreeSet::from(["fixture.cpp".into()]);
        let encoded = serde_json::to_value(corpus()).unwrap();
        let mut paths = vec![];
        identity_paths(&encoded, "", &mut paths);
        for path in paths {
            let mut forged = encoded.clone();
            *forged.pointer_mut(&path).unwrap() = json!("");
            let function = serde_json::from_value(forged).unwrap();
            assert!(
                check_function(&function, "fixture.cpp", &sources)
                    .unwrap_err()
                    .contains("identity"),
                "missed {path}"
            );
        }
    }

    #[test]
    fn metadata_work_scales_with_nodes_and_aliases_without_outer_environments() {
        let sources = BTreeSet::from(["fixture.cpp".into(), "types.hpp".into()]);
        for size in [4, 32, 256, 1024] {
            let statement = json!({"kind":"return_call","callee":reference(),"arguments":call_arguments(),"value_type":ty(),"cleanups":[cleanup()],"span":span()});
            let function = fixture(Value::Array(vec![statement; size]));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                check_function(&function, "fixture.cpp", &sources)
            });
            result.unwrap();
            assert_eq!(work, 4 + 16 * size);
        }
        // Type wrappers and aliases are structural; widths and pointee support
        // are left to the semantic validator. Alias provenance still matters.
        let mut value_type = ty();
        value_type["source_aliases"][0]["span"]["file"] = json!("types.hpp");
        let value_type: CppType = serde_json::from_value(
            json!({"kind":"lvalue_reference","pointee":{"kind":"pointer","pointee":value_type}}),
        )
        .unwrap();
        value_type.validate_aliases_in(&sources).unwrap();
        assert!(
            value_type
                .validate_aliases_in(&BTreeSet::from(["fixture.cpp".into()]))
                .is_err()
        );
        let mut cyclic = ty();
        let duplicate = cyclic["source_aliases"][0].clone();
        cyclic["source_aliases"]
            .as_array_mut()
            .unwrap()
            .push(duplicate);
        let cyclic: CppType = serde_json::from_value(cyclic).unwrap();
        assert!(
            cyclic
                .validate_aliases_in(&sources)
                .unwrap_err()
                .contains("cycle")
        );
    }
}
