use super::*;
use crate::surface::{ProgramVerificationSession, expand_program_prepared_claim_source_by_label};
use serde_json::{Value, json};

pub(super) fn fixture(parameter: &str) -> RustExport {
    let span = json!({"line": 1, "column": 1});
    let ty = json!({"kind": "i32"});
    serde_json::from_value(json!({
        "schema": super::super::schema::SCHEMA,
        "compiler_commit": "test", "target": super::super::schema::TARGET,
        "edition": "2021", "overflow_checks": true, "panic": "abort",
        "mir_opt_level": 0, "logical_source": "returns.rs", "records": [],
        "functions": [
            {"name": "identity", "return_type": ty,
             "parameters": [{"name": "value", "value_type": ty, "span": span}],
             "body": [{"kind": "return", "value": {"kind": "local", "name": "value"}}],
             "mir": null, "span": span},
            {"name": "caller", "return_type": ty,
             "parameters": [{"name": parameter, "value_type": ty, "span": span}],
             "body": [{"kind": "return", "value": {"kind": "call", "function": "identity",
                       "arguments": [{"kind": "local", "name": parameter}]}}],
             "mir": null, "span": span}
        ]
    }))
    .unwrap()
}

fn operations<'a>(statement: &'a ProgramStatement, result: &mut Vec<&'a ProgramStatement>) {
    match statement {
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                operations(statement, result);
            }
        }
        ProgramStatement::Skip => (),
        statement => result.push(statement),
    }
}

#[test]
fn returned_calls_use_step_results_without_declaring_a_return_local() {
    for parameter in ["value", "__rust_return_value", "__rust_return_value_"] {
        let export = fixture(parameter);
        let (functions, _) = super::lower(&export).unwrap();
        let caller = functions.iter().find(|f| f.name() == "caller").unwrap();
        assert_eq!(caller.parameters()[0].name(), parameter);
        let mut body = Vec::new();
        operations(
            caller.prelowered_kernel_function().unwrap().body(),
            &mut body,
        );
        assert_eq!(
            body.len(),
            2,
            "no declaration or assignment should be inserted"
        );
        assert!(
            matches!(body[0], ProgramStatement::CallResult { call: 0, function_name, .. } if function_name == "identity")
        );
        assert!(
            matches!(body[1], ProgramStatement::Return(ProgramExpression::StepResult {
            step: 0, origin: StepOrigin::Call(function), ends: true,
        }) if function == "identity")
        );
    }
}

#[test]
fn returned_calls_preserve_nested_argument_order_and_distinct_results() {
    let mut export = fixture("value");
    let mut second = export.functions[0].clone();
    second.name = "second".into();
    let mut choose = export.functions[0].clone();
    choose.name = "choose".into();
    let mut extra = choose.parameters[0].clone();
    extra.name = "ignored".into();
    choose.parameters.insert(0, extra);
    export.functions.extend([second, choose]);
    export.functions[1].body = vec![S::Return {
        value: Some(E::Call {
            function: "choose".into(),
            arguments: ["identity", "second"]
                .map(|function| E::Call {
                    function: function.into(),
                    arguments: vec![E::Local {
                        name: "value".into(),
                    }],
                })
                .into(),
        }),
    }];
    let (functions, _) = super::lower(&export).unwrap();
    let caller = functions.iter().find(|f| f.name() == "caller").unwrap();
    let mut body = Vec::new();
    operations(
        caller.prelowered_kernel_function().unwrap().body(),
        &mut body,
    );
    let calls = body
        .iter()
        .filter_map(|statement| match statement {
            ProgramStatement::CallResult {
                call,
                function_name,
                ..
            } => Some((*call, function_name.as_str())),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls, [(0, "identity"), (1, "second"), (2, "choose")]);
    assert!(
        matches!(body.last().unwrap(), ProgramStatement::Return(ProgramExpression::StepResult {
        step: 2, origin: StepOrigin::Call(function), ends: true,
    }) if function == "choose")
    );
}

#[test]
fn returned_call_results_verify_expand_and_reject_false_claims() {
    let prepared = super::super::import::prepared_for_test(fixture("value")).unwrap();
    let source = r#"verifying "returns.rs";
fn identity(value: i32) -> i32 { ensures result == value; }
fn caller(value: i32) -> i32 { ensures result == value; } by {
    step_until(function.exit);
    have call(identity, 0).result == value by close();
}
"#;
    ProgramVerificationSession::new_program_prepared(source, &prepared).unwrap();
    let expanded =
        expand_program_prepared_claim_source_by_label(source, &prepared, "caller.contract")
            .unwrap();
    assert!(expanded.contains("call(identity, 0).result"), "{expanded}");
    assert!(!expanded.contains("__rust_return_value"), "{expanded}");
    ProgramVerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
    let invalid = source.replace(
        "fn caller(value: i32) -> i32 { ensures result == value; }",
        "fn caller(value: i32) -> i32 { ensures result != value; }",
    );
    assert_ne!(invalid, source);
    assert!(ProgramVerificationSession::new_program_prepared(&invalid, &prepared).is_err());
}

#[test]
fn short_circuit_arms_publish_one_result_and_replay() {
    use crate::surface::{
        ProgramVerificationSession, expand_program_prepared_claim_source_by_label,
        without_implicit_solve_for_claim,
    };

    for (operator, expected) in [("and", "false"), ("or", "true")] {
        let mut export = fixture("value");
        for function in &mut export.functions {
            function.parameters[0].value_type = Type::Bool;
            function.return_type = Type::Bool;
        }
        export.functions[1].body = vec![S::Return {
            value: Some(E::Binary {
                operator: operator.into(),
                left_type: Type::Bool,
                right_type: Type::Bool,
                left: Box::new(E::Local {
                    name: "value".into(),
                }),
                right: Box::new(E::Call {
                    function: "identity".into(),
                    arguments: vec![E::Not {
                        value: Box::new(E::Local {
                            name: "value".into(),
                        }),
                    }],
                }),
            }),
        }];
        let (functions, _) = super::lower(&export).unwrap();
        let caller = functions.iter().find(|f| f.name() == "caller").unwrap();
        let body = format!("{:?}", caller.prelowered_kernel_function().unwrap().body());
        assert!(!body.contains("__rust_checked_"), "{body}");
        let prepared = super::super::import::prepared_for_test(export).unwrap();
        let source = format!(
            r#"verifying "returns.rs";
fn identity(value: bool) -> bool {{ ensures result == value; }}
fn caller(value: bool) -> bool {{ ensures result == {expected}; }}
"#
        );
        let claim = "caller.ensures_0";
        let expanded = expand_program_prepared_claim_source_by_label(&source, &prepared, claim)
            .unwrap_or_else(|error| panic!("{}", error.report()));
        assert!(!expanded.contains("__rust_checked_"), "{expanded}");
        without_implicit_solve_for_claim(claim, || {
            ProgramVerificationSession::new_program_prepared(&expanded, &prepared)
                .map(|_| ())
                .map_err(|error| error.report())
        })
        .unwrap();
    }
}

/// A claim selected by its Rust path is the one the checker enters under
/// its importer name, so checking it with the implicit closer off visits it.
#[test]
fn a_claim_selected_by_its_rust_path_is_checked_without_the_closer() {
    use crate::languages::rust::names::path_name;
    use crate::surface::without_implicit_solve_for_claim;

    let mut export = fixture("value");
    let identity = path_name(&["quad", "identity"]);
    export.functions[0].name = identity.clone();
    export.functions[1].name = path_name(&["quad", "caller"]);
    export.functions[1].body = vec![S::Return {
        value: Some(E::Call {
            function: identity,
            arguments: vec![E::Local {
                name: "value".into(),
            }],
        }),
    }];
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    let source = r#"verifying "returns.rs";
fn quad::identity(value: i32) -> i32 { ensures result == value; }
fn quad::caller(value: i32) -> i32 { ensures result == value; } by {
    step_until(function.exit);
}
"#;
    let claim = "quad::caller.contract";
    let expanded = expand_program_prepared_claim_source_by_label(source, &prepared, claim)
        .unwrap_or_else(|error| panic!("{}", error.report()));
    without_implicit_solve_for_claim(claim, || {
        ProgramVerificationSession::new_program_prepared(&expanded, &prepared)
            .map(|_| ())
            .map_err(|error| error.report())
    })
    .unwrap();
}

fn local(name: &str) -> Value {
    json!({"kind":"local", "name":name})
}
fn integer(value: i32) -> Value {
    json!({"kind":"integer", "value":value})
}
fn binary(operator: &str, ty: &str, left: Value, right: Value) -> Value {
    json!({"kind":"binary", "operator":operator, "left_type":{"kind":ty}, "right_type":{"kind":ty}, "left":left, "right":right})
}
fn returned(value: Value) -> S {
    serde_json::from_value(json!({"kind":"return", "value":value})).unwrap()
}
fn verify_operand_expansion(export: RustExport, source: &str) {
    let prepared = super::super::import::prepared_for_test(export).unwrap();
    ProgramVerificationSession::new_program_prepared(source, &prepared).unwrap();
    let expanded =
        expand_program_prepared_claim_source_by_label(source, &prepared, "caller.contract")
            .unwrap();
    assert!(!expanded.contains("__rust_checked_"), "{expanded}");
    ProgramVerificationSession::new_program_prepared(&expanded, &prepared).unwrap();
}

#[test]
fn operand_capture_keeps_the_read_before_a_mutating_call() {
    let mut export = fixture("unused");
    let span = json!({"line":1,"column":1});
    export.functions[0] = serde_json::from_value(json!({
        "name":"bump", "return_type":{"kind":"i32"},
        "parameters":[{"name":"target", "value_type":{"kind":"reference", "mutable":true, "pointee":{"kind":"i32"}}, "span":span}],
        "body":[{"kind":"assign", "target":{"kind":"deref", "reference":local("target"), "value_type":{"kind":"i32"}}, "value":integer(9)},
                {"kind":"return", "value":integer(2)}], "mir":null, "span":span
    })).unwrap();
    export.functions[1].parameters = export.functions[0].parameters.clone();
    export.functions[1].body = vec![returned(binary(
        "add",
        "i32",
        json!({"kind":"deref", "reference":local("target"), "value_type":{"kind":"i32"}}),
        json!({"kind":"call", "function":"bump", "arguments":[local("target")]}),
    ))];
    verify_operand_expansion(
        export,
        r#"verifying "returns.rs";
fn bump(target: &mut i32) -> i32 { owns *target; ensures *target == 9; ensures result == 2; }
fn caller(target: &mut i32) -> i32 { owns *target; requires *target == 1; ensures *target == 9; ensures result == 3; } by { step_until(function.exit); close(); }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: Rust array-repeat expansion"]
fn array_repeat_evaluates_its_operand_once_including_zero_elements() {
    for length in [0, 3] {
        let mut export = fixture("unused");
        let span = json!({"line":1,"column":1});
        let deref =
            json!({"kind":"deref", "reference":local("target"), "value_type":{"kind":"i32"}});
        export.functions[0] = serde_json::from_value(json!({
            "name":"tick", "return_type":{"kind":"i32"},
            "parameters":[{"name":"target", "value_type":{"kind":"reference", "mutable":true, "pointee":{"kind":"i32"}}, "span":span}],
            "body":[{"kind":"assign", "target":deref, "value":binary("add", "i32", deref.clone(), integer(1))},
                    {"kind":"return", "value":integer(2)}], "mir":null, "span":span
        })).unwrap();
        export.functions[1].parameters = export.functions[0].parameters.clone();
        export.functions[1].body = vec![
            serde_json::from_value(json!({"kind":"declare", "place":{"name":"items", "value_type":{"kind":"array", "element":{"kind":"i32"}, "length":length}, "span":span},
                "initializer":{"kind":"repeat", "length":length, "value":{"kind":"call", "function":"tick", "arguments":[local("target")]}}})).unwrap(),
            returned(deref),
        ];
        verify_operand_expansion(
            export,
            r#"verifying "returns.rs";
fn tick(target: &mut i32) -> i32 { owns *target; requires *target >= 0; requires *target < 10; ensures *target == old(*target) + 1; ensures result == 2; }
fn caller(target: &mut i32) -> i32 { owns *target; requires *target == 1; ensures *target == 2; ensures result == 2; } by { step_until(function.exit); close(); }
"#,
        );
    }
}
