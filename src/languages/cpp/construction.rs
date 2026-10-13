//! Source restriction justifying construction-return lowering across C++20's
//! permitted trivial parameter/result copies ([class.temporary]).
//!
//! Eligible constructors write only their fields from evaluated argument values.
//! They neither read aliasable memory nor expose their own storage. Constructing
//! in another object and trivially copying its fields therefore preserves the
//! observable values, including pointer values, through any permitted copy chain.
//! This is a frontend admission check; constructor contracts remain body-checked.

use super::schema::RecordIndex;
use super::{
    CppCallArgument, CppCondition, CppExpression, CppFunction, CppFunctionKind,
    CppFunctionReference, CppInitializer, CppStatement, CppType,
};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn is_construction_return(function: &CppFunction) -> bool {
    // An axiom returning a record constructs it into the caller's
    // destination; its contract describes the constructed value.
    if function.axiom.is_some() {
        return matches!(function.return_type, super::CppType::Record { .. });
    }
    statements(&function.body).any(|statement| {
        matches!(
            statement,
            CppStatement::ReturnConstruct { .. } | CppStatement::ReturnAggregateCall { .. }
        )
    })
}

fn statements(body: &[CppStatement]) -> impl Iterator<Item = &CppStatement> {
    let mut pending = vec![body.iter()];
    std::iter::from_fn(move || {
        loop {
            let current = pending.last_mut()?.next();
            let Some(statement) = current else {
                pending.pop();
                continue;
            };
            match statement {
                CppStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(else_branch.iter());
                    pending.push(then_branch.iter());
                }
                CppStatement::Scope { body, .. } => pending.push(body.iter()),
                CppStatement::TryCatchInt32 {
                    try_body, handler, ..
                } => {
                    pending.push(handler.iter());
                    pending.push(try_body.iter());
                }
                _ => {}
            }
            return Some(statement);
        }
    })
}

pub(super) fn validate_returns<'a>(
    functions: &BTreeMap<String, &'a CppFunction>,
    records: &RecordIndex<'a>,
) -> Result<(), String> {
    let modes = functions
        .iter()
        .map(|(id, function)| (id.as_str(), is_construction_return(function)))
        .collect::<BTreeMap<_, _>>();
    let mut eligibility = Eligibility {
        functions,
        records,
        checked: BTreeMap::new(),
    };
    for function in functions.values() {
        for (callee, constructing) in super::schema::prvalue_argument_calls(function) {
            if constructing {
                if !eligibility.function(callee)? {
                    return Err(format!(
                        "C++ record prvalue argument constructor `{}` is not copy-equivalent: storage addresses, memory reads or external effects remain outside the profile",
                        callee.name
                    ));
                }
            } else {
                let target = functions
                    .get(&callee.declaration_id)
                    .ok_or("C++ aggregate prvalue argument has no reachable definition")?;
                if !modes[callee.declaration_id.as_str()] || !target.declared_noexcept {
                    return Err("C++ aggregate prvalue arguments require admitted nonthrowing construction-return callees".into());
                }
            }
        }
        let mut construction = false;
        let mut copying = false;
        for statement in statements(&function.body) {
            crate::instrumentation::record_deterministic_work(1);
            match statement {
                CppStatement::ReturnConstruct { callee, .. } => {
                    construction = true;
                    if !eligibility.function(callee)? {
                        return Err(format!(
                            "C++ returned constructor `{}` must use only argument values without memory reads, storage addresses or runtime effects",
                            callee.name
                        ));
                    }
                }
                CppStatement::ReturnAggregateCall { callee, .. } => {
                    construction = true;
                    let target = functions
                        .get(&callee.declaration_id)
                        .ok_or("C++ aggregate return call has no reachable definition")?;
                    if !modes[callee.declaration_id.as_str()] || !target.declared_noexcept {
                        return Err("C++ aggregate forwarding requires an admitted nonthrowing construction-return callee".into());
                    }
                }
                CppStatement::Declare {
                    initializer: CppInitializer::ConstructionCall { callee, .. },
                    ..
                }
                | CppStatement::AssignConstructionCall { callee, .. } => {
                    let target = functions
                        .get(&callee.declaration_id)
                        .ok_or("C++ construction initializer has no reachable definition")?;
                    if !modes[callee.declaration_id.as_str()] || !target.declared_noexcept {
                        return Err("C++ construction initialization requires an admitted nonthrowing construction-return callee".into());
                    }
                }
                CppStatement::ReturnRecord { .. } => copying = true,
                _ => {}
            }
        }
        if construction && (copying || !function.declared_noexcept) {
            return Err("C++ construction returns require noexcept and cannot mix with copy-return branches".into());
        }
    }
    Ok(())
}

struct Eligibility<'a, 'g> {
    functions: &'g BTreeMap<String, &'a CppFunction>,
    records: &'g RecordIndex<'a>,
    checked: BTreeMap<String, bool>,
}

impl Eligibility<'_, '_> {
    fn function(&mut self, reference: &CppFunctionReference) -> Result<bool, String> {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(result) = self.checked.get(&reference.declaration_id) {
            return Ok(*result);
        }
        let function = *self
            .functions
            .get(&reference.declaration_id)
            .ok_or("C++ construction eligibility found an unknown callee")?;
        // Graph validation already rejects recursion and bounds depth. Also
        // refuse a recursive eligibility dependency if called independently.
        self.checked.insert(reference.declaration_id.clone(), false);
        // This is admission of the explicit copy-equivalent model recipe,
        // never of the exported axiom's empty body. Actual model selection
        // additionally binds the locked header/profile/layout before execution.
        let result = if super::library_models::candidate(function)
            == Some(super::library_models::Model::WordConstructor)
        {
            true
        } else {
            self.body(function)?
        };
        self.checked
            .insert(reference.declaration_id.clone(), result);
        Ok(result)
    }

    fn body(&mut self, function: &CppFunction) -> Result<bool, String> {
        if !function.declared_noexcept {
            return Ok(false);
        }
        let constructor = matches!(function.function_kind, CppFunctionKind::Constructor { .. });
        let parameters = function.parameters.iter().skip(usize::from(constructor));
        let mut values = BTreeSet::new();
        for parameter in parameters {
            if !matches!(
                parameter.value_type,
                CppType::Integer { .. } | CppType::Boolean { .. } | CppType::Pointer { .. }
            ) {
                return Ok(false);
            }
            values.insert(parameter.declaration_id.as_str());
        }
        if let CppFunctionKind::Constructor {
            record_declaration_id,
            ..
        } = &function.function_kind
        {
            let record = self
                .records
                .get(record_declaration_id)
                .ok_or("C++ construction eligibility found an unknown record")?;
            if record.base.is_some() || record.destructor.is_some() {
                return Ok(false);
            }
            let Some((prefix, rest)) = function.body.split_at_checked(record.fields.len()) else {
                return Ok(false);
            };
            for statement in prefix {
                crate::instrumentation::record_deterministic_work(1);
                let valid = match statement {
                    CppStatement::MemberStore { value, .. } => self.value(value, &values)?,
                    CppStatement::MemberConstruct {
                        callee, arguments, ..
                    } => self.arguments(arguments, &values)? && self.function(callee)?,
                    _ => false,
                };
                if !valid {
                    return Ok(false);
                }
            }
            self.empty_runtime(rest, &values)
        } else if matches!(
            function.function_kind,
            CppFunctionKind::Free | CppFunctionKind::StaticMethod { .. }
        ) && matches!(
            function.return_type,
            CppType::Integer { .. } | CppType::Boolean { .. } | CppType::Pointer { .. }
        ) {
            match function.body.as_slice() {
                [
                    CppStatement::Return {
                        value, cleanups, ..
                    },
                ] if cleanups.is_empty() => self.value(value, &values),
                [
                    CppStatement::ReturnCall {
                        callee,
                        arguments,
                        cleanups,
                        ..
                    },
                ] if cleanups.is_empty() => {
                    Ok(self.arguments(arguments, &values)? && self.function(callee)?)
                }
                _ => Ok(false),
            }
        } else {
            Ok(false)
        }
    }

    fn arguments(
        &mut self,
        arguments: &[CppCallArgument],
        values: &BTreeSet<&str>,
    ) -> Result<bool, String> {
        for argument in arguments {
            let valid = match argument {
                CppCallArgument::Value { value } => self.value(value, values)?,
                CppCallArgument::Call {
                    callee, arguments, ..
                } => self.arguments(arguments, values)? && self.function(callee)?,
                CppCallArgument::Reference { .. }
                | CppCallArgument::RecordCopy { .. }
                | CppCallArgument::RecordConstruct { .. } => false,
            };
            if !valid {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn value(&mut self, value: &CppExpression, values: &BTreeSet<&str>) -> Result<bool, String> {
        crate::instrumentation::record_deterministic_work(1);
        Ok(match value {
            CppExpression::IntegerLiteral { .. }
            | CppExpression::NullPointer { .. }
            | CppExpression::CompilerConstant { .. }
            | CppExpression::ConstantReference { .. }
            | CppExpression::RuntimeConstantEvaluation { .. } => true,
            CppExpression::Load { place, .. } => {
                place.projections.is_empty() && values.contains(place.declaration_id.as_str())
            }
            CppExpression::LogicalNot { value, .. }
            | CppExpression::IntegralCast { value, .. }
            | CppExpression::EnumCast { value, .. }
            | CppExpression::BytePointerCast { value, .. } => self.value(value, values)?,
            CppExpression::Binary { left, right, .. } => {
                self.value(left, values)? && self.value(right, values)?
            }
            CppExpression::ObserverCall {
                callee, arguments, ..
            } => self.arguments(arguments, values)? && self.function(callee)?,
            CppExpression::AddressOf { .. }
            | CppExpression::ReferenceBinding { .. }
            | CppExpression::Dereference { .. }
            | CppExpression::MemberLoad { .. } => false,
        })
    }

    fn empty_runtime(
        &mut self,
        body: &[CppStatement],
        values: &BTreeSet<&str>,
    ) -> Result<bool, String> {
        for statement in body {
            crate::instrumentation::record_deterministic_work(1);
            let valid = match statement {
                CppStatement::If {
                    condition: CppCondition::Expression(condition),
                    then_branch,
                    else_branch,
                    ..
                } => {
                    if !self.value(condition, values)? {
                        return Ok(false);
                    }
                    match runtime_boolean(condition) {
                        Some(true) => self.empty_runtime(then_branch, values)?,
                        Some(false) => self.empty_runtime(else_branch, values)?,
                        None => {
                            self.empty_runtime(then_branch, values)?
                                && self.empty_runtime(else_branch, values)?
                        }
                    }
                }
                CppStatement::Scope { body, cleanups, .. } if cleanups.is_empty() => {
                    self.empty_runtime(body, values)?
                }
                _ => false,
            };
            if !valid {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

fn runtime_boolean(value: &CppExpression) -> Option<bool> {
    match value {
        CppExpression::RuntimeConstantEvaluation { .. } => Some(false),
        CppExpression::LogicalNot { value, .. } => runtime_boolean(value).map(|value| !value),
        CppExpression::IntegralCast {
            value,
            value_type: CppType::Boolean { .. },
            ..
        } => match value.as_ref() {
            CppExpression::CompilerConstant { value, .. }
            | CppExpression::IntegerLiteral { value, .. } => match value.as_str() {
                "0" => Some(false),
                "1" => Some(true),
                _ => None,
            },
            value => runtime_boolean(value),
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::super::CppRecord;
    use super::*;
    use serde_json::json;

    // Many factories and fields share one helper/constructor. Rewalking that
    // constructor for every factory would make this import analysis quadratic.
    #[test]
    fn construction_eligibility_shares_transitive_body_work() {
        for size in [8, 32, 128] {
            let span = json!({"file":"fixture.cpp", "start_line":1, "start_column":1, "end_line":1, "end_column":2});
            let integer = json!({"kind":"integer", "bits":32, "signed":true, "is_const":false, "source_aliases":[]});
            let nominal =
                json!({"kind":"record", "declaration_id":"Box", "name":"Box", "is_const":false});
            let reference = |id: &str| json!({"declaration_id":id, "name":id, "span":span});
            let place = |id: &str, ty: &serde_json::Value| json!({"declaration_id":id, "name":id, "value_type":ty, "span":span});
            let load = |id: &str| json!({"kind":"load", "place":reference(id), "value_type":integer, "span":span});
            let fields = (0..size).map(|index| json!({"declaration_id":format!("field_{index}"), "name":format!("field_{index}"),
                "value_type":integer, "offset_bytes":index*4, "size_bytes":4, "span":span})).collect::<Vec<_>>();
            let record: CppRecord = serde_json::from_value(
                json!({"declaration_id":"Box", "name":"Box", "size_bytes":size*4,
                "alignment_bytes":4, "fields":fields, "destructor":null, "span":span}),
            )
            .unwrap();
            let body = fields.iter().map(|field| json!({"kind":"member_store", "object":reference("self"),
                "field":{"record_declaration_id":"Box", "declaration_id":field["declaration_id"], "name":field["name"], "span":span},
                "value":{"kind":"observer_call", "callee":reference("identity"), "arguments":[{"kind":"value", "value":load("input")}],
                    "value_type":integer, "span":span}, "span":span})).collect::<Vec<_>>();
            let constructor: CppFunction = serde_json::from_value(json!({"declaration_id":"construct", "name":"construct",
                "function_kind":{"kind":"constructor", "record_declaration_id":"Box", "record_name":"Box"},
                "return_type":{"kind":"void"}, "parameters":[place("self", &json!({"kind":"lvalue_reference", "pointee":nominal})), place("input", &integer)],
                "declared_noexcept":true, "span":span, "body":body})).unwrap();
            let helper: CppFunction = serde_json::from_value(json!({"declaration_id":"identity", "name":"identity", "function_kind":{"kind":"free"},
                "return_type":integer, "parameters":[place("input", &integer)], "declared_noexcept":true, "span":span,
                "body":[{"kind":"return", "value":load("input"), "cleanups":[], "span":span}]})).unwrap();
            let factories = (0..size).map(|index| serde_json::from_value::<CppFunction>(json!({"declaration_id":format!("factory_{index}"),
                "name":format!("factory_{index}"), "function_kind":{"kind":"free"}, "return_type":nominal,
                "parameters":[place("input", &integer)], "declared_noexcept":true, "span":span,
                "body":[{"kind":"return_construct", "callee":reference("construct"), "arguments":[{"kind":"value", "value":load("input")}],
                    "value_type":nominal, "cleanups":[], "span":span}]})).unwrap()).collect::<Vec<_>>();
            let functions = std::iter::once(&constructor)
                .chain(std::iter::once(&helper))
                .chain(&factories)
                .map(|function| (function.declaration_id.clone(), function))
                .collect();
            let records = RecordIndex::new(BTreeMap::from([("Box".into(), &record)]));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                validate_returns(&functions, &records)
            });
            result.unwrap();
            assert!(work >= size && work <= 16 * size + 32, "{size}: {work}");
        }
    }
}
