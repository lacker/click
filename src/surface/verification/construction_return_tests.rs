use super::c_frontend::parse_c_source_unit;
use super::*;
use crate::kernel::*;

// This is a typed-frontend integration fixture, not C++ source admission.
// The source supplies nominal declarations only; the executable functions
// explicitly select the shared construction-return mode.
fn context(initialize_value: bool) -> ProgramSourceContext<'static> {
    context_with_member_view(initialize_value, true)
}

fn context_with_member_view(
    initialize_value: bool,
    select_member: bool,
) -> ProgramSourceContext<'static> {
    const DECLARATIONS: &str = "struct Node { int32* self; int32 value; };";
    let sources = ProgramSourceContext::bundle(&[("construction.c", DECLARATIONS)]);
    let mut unit = parse_c_source_unit("construction.c", &sources, CTarget::SUPPORTED).unwrap();
    let nominal = unit.structs["Node"].clone();
    let layout = nominal.to_kernel_aggregate_layout();
    let member = nominal.field("value").unwrap();
    let destination = crate::kernel::program_expression::variable(CONTRACT_RESULT);
    let field = crate::kernel::program_expression::cast(
        crate::kernel::program_expression::pointer_offset_bytes(
            destination.clone(),
            member.offset_bytes(),
        ),
        ProgramType::Int32Pointer,
    );
    // Model &result.value, including its selected member bounds. A raw
    // offset has the same address but retains the enclosing object's view.
    let field = if select_member {
        ProgramExpression::Subobject {
            pointer: Box::new(field),
            width: member.byte_width(),
        }
    } else {
        field
    };
    let factory = program_function(
        ProgramType::Int32Pointer,
        "factory",
        vec![program_parameter("input", ProgramType::Int32)],
        program_seq(
            program_typed_store(
                destination.clone(),
                field.clone(),
                ProgramType::Int32Pointer,
            ),
            program_seq(
                if initialize_value {
                    program_typed_store(
                        field,
                        crate::kernel::program_expression::variable("input"),
                        ProgramType::Int32,
                    )
                } else {
                    program_skip()
                },
                program_return(destination.clone()),
            ),
        ),
    )
    .with_construction_return(layout.clone());
    let forward = program_function(
        ProgramType::Int32Pointer,
        "forward",
        vec![program_parameter("input", ProgramType::Int32)],
        program_seq(
            program_call_construct(
                CONTRACT_RESULT,
                "factory",
                vec![crate::kernel::program_expression::variable("input")],
            ),
            program_return(destination),
        ),
    )
    .with_construction_return(layout.clone());
    let caller = program_function(
        ProgramType::Int32,
        "probe",
        vec![program_parameter("input", ProgramType::Int32)],
        program_seq(
            program_allocate_aggregate_destination("node", layout),
            program_seq(
                program_call_construct(
                    "node",
                    "forward",
                    vec![crate::kernel::program_expression::variable("input")],
                ),
                program_return(crate::kernel::program_expression::load(
                    crate::kernel::program_expression::typed_load(
                        crate::kernel::program_expression::variable("node"),
                        ProgramType::Int32Pointer,
                    ),
                )),
            ),
        ),
    );
    let parameters = || {
        vec![crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "input".into(),
            None,
        )]
    };
    unit.functions = vec![
        crate::languages::interface::ImportedFunction::external(
            InterfaceType::Int32Pointer,
            "factory".into(),
            parameters(),
        )
        .with_struct_return("Node".into(), nominal.clone())
        .with_prelowered_kernel_function(factory),
        crate::languages::interface::ImportedFunction::external(
            InterfaceType::Int32Pointer,
            "forward".into(),
            parameters(),
        )
        .with_struct_return("Node".into(), nominal.clone())
        .with_prelowered_kernel_function(forward),
        crate::languages::interface::ImportedFunction::external(
            InterfaceType::Int32,
            "probe".into(),
            parameters(),
        )
        .with_prelowered_kernel_function(caller)
        .with_local_struct_values(BTreeMap::from([("node".into(), "Node".into())])),
    ];
    sources
        .parsed_units
        .borrow_mut()
        .insert("construction.c".into(), Arc::new(unit));
    sources
}

const PROOF: &str = r#"verifying "construction.c";
struct Node factory(int32 input) {
 ensures result.self == &result.value;
 ensures result.value == input;
}
struct Node forward(int32 input) {
 ensures result.self == &result.value;
 ensures result.value == input;
}
int32 probe(int32 input) {
 ensures result == input;
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn native_construction_return_contracts_forward_hidden_storage() {
    let sources = context(true);
    let (verified, environment) =
        verify_program_with_context(PROOF, &sources, None, None, None, None).unwrap();
    // Exercise the same retained-environment path as a selected proof edit.
    let _tables = crate::kernel::VerificationSession::resume();
    for name in ["factory", "forward", "probe"] {
        verify_program_with_context(
            PROOF,
            &sources,
            Some(VerificationTarget::Function(name.into())),
            Some(environment.clone().without_verified_function_rule(name)),
            None,
            None,
        )
        .unwrap();
    }
    let mut expanded = PROOF.to_string();
    for name in ["factory", "forward", "probe"] {
        let theorem = verified
            .iter()
            .find(|theorem| theorem.function_block.signature().name() == name)
            .unwrap();
        expanded = expanded.replacen(
            "by { step_until(function.exit); close(); }",
            &theorem.expanded_proof_source().unwrap(),
            1,
        );
    }
    verify_program_with_context(&expanded, &sources, None, None, None, None).unwrap();
}

#[test]
fn native_construction_return_member_addresses_bind_result() {
    let source = r#"verifying "construction.c";
struct Node factory(int32 input) {
    ensures address(result.self) == address(&result.value);
    ensures result.value == input;
}
"#;
    let sources = context(true);
    let (verified, environment) =
        verify_program_with_context(source, &sources, None, None, None, None).unwrap();
    let _tables = crate::kernel::VerificationSession::resume();
    verify_program_with_context(
        source,
        &sources,
        Some(VerificationTarget::Function("factory".into())),
        Some(environment.without_verified_function_rule("factory")),
        None,
        None,
    )
    .unwrap();
    let expanded = source.replacen(
        "by { step_until(function.exit); close(); }",
        &verified[0].expanded_proof_source().unwrap(),
        1,
    );
    verify_program_with_context(&expanded, &sources, None, None, None, None).unwrap();
}

#[test]
fn native_construction_return_keeps_raw_offset_and_member_views_distinct() {
    let sources = context_with_member_view(true, false);
    let error = verify_program_with_context(
        PROOF,
        &sources,
        Some(VerificationTarget::Function("factory".into())),
        None,
        None,
        None,
    )
    .expect_err("a raw offset is not the full pointer selected by &result.value");
    assert!(
        error.message().contains("factory.ensures_0"),
        "{}",
        error.message()
    );
}

// The hidden resource needs no written storage clause, but returning it must
// not mark an unwritten field initialized. Keep the value claim independent
// of the fields so this exercises construction completion itself.
#[test]
fn native_construction_return_contracts_require_complete_initialization() {
    let safety_only = r#"verifying "construction.c";
struct Node factory(int32 input) { ensures input == input; }
"#;
    let sources = context(true);
    verify_program_with_context(safety_only, &sources, None, None, None, None).unwrap();
    let sources = context(false);
    assert!(verify_program_with_context(safety_only, &sources, None, None, None, None).is_err());
}
