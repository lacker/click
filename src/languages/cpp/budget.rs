//! Resource policy, independent of artifact correctness and C++ semantics.
//!
//! Check serialized nesting before deserialization or recursive semantic walks.
//! This scanner does not establish JSON validity; serde still checks the grammar.

use super::CppExport;

pub(super) const MAX_RECORDS: usize = 256;
pub(super) const MAX_RECORD_LAYOUT_LEAVES: usize = 65_536;
pub(super) const MAX_CONSTANTS: usize = 1024;
pub(super) const MAX_FUNCTIONS: usize = 1024;
pub(super) const MAX_CALL_DEPTH: usize = 64;
pub(super) const MAX_SCALAR_CONVERSIONS: usize = 256;
pub(super) const MAX_LOCAL_DECLARATIONS: usize = 1024;
pub(super) const MAX_CLEANUP_SCOPES: usize = 256;
const MAX_JSON_CONTAINERS: usize = 65_536;
const MAX_JSON_NESTING: usize = 96;

pub(super) fn limit(name: &str, observed: usize, maximum: usize) -> Result<(), String> {
    if observed > maximum {
        Err(format!(
            "C++ artifact budget exhausted: {name} ({observed} > {maximum})"
        ))
    } else {
        Ok(())
    }
}

pub(super) fn check_inventories(export: &CppExport) -> Result<(), String> {
    limit("record declarations", export.records.len(), MAX_RECORDS)?;
    limit(
        "constant declarations",
        export.constants.len(),
        MAX_CONSTANTS,
    )?;
    limit(
        "function declarations",
        export.reachable_functions.len() + 1,
        MAX_FUNCTIONS,
    )
}

// Count syntax once, independently of supported lifetime combinations. Catch
// bindings count as local declarations; parameters do not. Both if arms count
// even when only one can execute, so branching cannot hide an exhausted budget.
pub(super) fn check_function(function: &super::schema::CppFunction) -> Result<(), String> {
    use super::schema::CppStatement;
    let mut locals = 0;
    let mut scopes = 0;
    let mut pending = vec![function.body.as_slice()];
    while let Some(body) = pending.pop() {
        for statement in body {
            crate::instrumentation::record_deterministic_work(1);
            match statement {
                CppStatement::Declare { .. } => locals += 1,
                CppStatement::Scope { body, .. } => {
                    scopes += 1;
                    pending.push(body);
                }
                CppStatement::TryCatchInt32 {
                    try_body, handler, ..
                } => {
                    locals += 1;
                    pending.push(try_body);
                    pending.push(handler);
                }
                CppStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    pending.push(then_branch);
                    pending.push(else_branch);
                }
                _ => {}
            }
            limit(
                "local declarations per function",
                locals,
                MAX_LOCAL_DECLARATIONS,
            )?;
            limit("cleanup scopes per function", scopes, MAX_CLEANUP_SCOPES)?;
        }
    }
    Ok(())
}

pub(super) fn check_serialized(bytes: &[u8]) -> Result<(), String> {
    let mut quoted = false;
    let mut escaped = false;
    let mut nesting = 0usize;
    let mut containers = 0usize;
    crate::instrumentation::record_deterministic_work(bytes.len());
    for &byte in bytes {
        if quoted {
            if escaped {
                escaped = false;
            } else if byte == b'\\' {
                escaped = true;
            } else if byte == b'"' {
                quoted = false;
            }
        } else {
            match byte {
                b'"' => quoted = true,
                b'{' | b'[' => {
                    nesting += 1;
                    containers += 1;
                    limit("serialized nesting", nesting, MAX_JSON_NESTING)?;
                    limit("serialized containers", containers, MAX_JSON_CONTAINERS)?;
                }
                b'}' | b']' => nesting = nesting.saturating_sub(1),
                _ => {}
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(body: Vec<super::super::schema::CppStatement>) -> super::super::schema::CppFunction {
        use super::super::schema::*;
        CppFunction {
            template_record_arguments: vec![],
            axiom: None,
            declaration_id: "root".into(),
            name: "root".into(),
            function_kind: CppFunctionKind::Free,
            return_type: CppType::Void,
            parameters: vec![],
            declared_noexcept: false,
            span: CppSpan {
                file: "fixture.cpp".into(),
                start_line: 1,
                start_column: 1,
                end_line: 1,
                end_column: 2,
            },
            body,
        }
    }

    #[test]
    fn function_budgets_count_both_arms_and_catch_bindings_without_environment_copies() {
        use super::super::schema::*;
        let span = fixture(vec![]).span;
        let place = CppPlace {
            declaration_id: "local".into(),
            name: "local".into(),
            value_type: CppType::Integer {
                bits: 32,
                signed: true,
                is_const: false,
                source_aliases: vec![],
            },
            span: span.clone(),
        };
        let value = CppExpression::IntegerLiteral {
            value: "0".into(),
            value_type: place.value_type.clone(),
            span: span.clone(),
        };
        let declaration = CppStatement::Declare {
            local: place.clone(),
            initializer: CppInitializer::Value {
                value: value.clone(),
            },
            span: span.clone(),
        };
        for size in [4, 32, 256, MAX_LOCAL_DECLARATIONS] {
            let mut function = fixture(vec![declaration.clone(); size]);
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| check_function(&function));
            result.unwrap();
            assert_eq!(work, size);
            function.body.push(CppStatement::TryCatchInt32 {
                try_body: vec![],
                binding: place.clone(),
                handler: vec![],
                span: span.clone(),
            });
            if size == MAX_LOCAL_DECLARATIONS {
                assert!(
                    check_function(&function)
                        .unwrap_err()
                        .contains("local declarations per function")
                );
            } else {
                check_function(&function).unwrap();
            }
        }
        let scope = CppStatement::Scope {
            body: vec![declaration.clone()],
            cleanups: vec![],
            span: span.clone(),
        };
        for size in [4, 16, 64, MAX_CLEANUP_SCOPES] {
            let function = fixture(vec![scope.clone(); size]);
            let (result, work) =
                crate::instrumentation::measure_deterministic_work(|| check_function(&function));
            result.unwrap();
            assert_eq!(work, 2 * size);
        }
        let both_arms = CppStatement::If {
            condition: value.into(),
            then_branch: vec![scope.clone(); MAX_CLEANUP_SCOPES / 2],
            else_branch: vec![scope; MAX_CLEANUP_SCOPES / 2 + 1],
            span: span.clone(),
        };
        assert!(
            check_function(&fixture(vec![both_arms]))
                .unwrap_err()
                .contains("cleanup scopes per function")
        );
        let nested = CppStatement::Scope {
            body: vec![declaration; MAX_LOCAL_DECLARATIONS + 1],
            cleanups: vec![],
            span,
        };
        assert!(
            check_function(&fixture(vec![nested]))
                .unwrap_err()
                .contains("local declarations per function")
        );
    }

    #[test]
    fn serialized_budget_counts_containers_without_interpreting_strings() {
        let escaped = serde_json::to_vec(&"[{}]\\\"[{}]").unwrap();
        check_serialized(&escaped).unwrap();
        let nesting = vec![b'['; MAX_JSON_NESTING + 1];
        assert!(
            check_serialized(&nesting)
                .unwrap_err()
                .contains("serialized nesting")
        );
        let containers = "[],".repeat(MAX_JSON_CONTAINERS + 1);
        assert!(
            check_serialized(containers.as_bytes())
                .unwrap_err()
                .contains("serialized containers")
        );
        // Budget checks do not turn malformed input into an accepted artifact.
        check_serialized(b"{]").unwrap();
        assert!(serde_json::from_slice::<CppExport>(b"{]").is_err());
    }

    #[test]
    fn serialized_budget_work_is_linear_in_input_bytes() {
        for size in [8, 32, 128, 512] {
            let input = format!("[{}]", "{},".repeat(size));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                check_serialized(input.as_bytes())
            });
            result.unwrap();
            assert_eq!(work, input.len());
        }
    }

    #[test]
    fn named_inventory_budgets_accept_the_boundary_and_reject_the_next_entry() {
        for (name, maximum) in [
            ("record declarations", MAX_RECORDS),
            ("constant declarations", MAX_CONSTANTS),
            ("function declarations", MAX_FUNCTIONS),
        ] {
            limit(name, maximum, maximum).unwrap();
            assert!(
                limit(name, maximum + 1, maximum)
                    .unwrap_err()
                    .contains(name)
            );
        }
    }
}
