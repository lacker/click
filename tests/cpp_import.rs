use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};
#[cfg(not(feature = "fast-gate"))]
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use click::cli::{VerificationInput, parse_mdtest, read_click_project, read_verification_inputs};
use click::kernel::{
    Address, AddressOffset, ExecutionState, FunctionOutcome, MachineTerm, MemoryRange,
    ProgramExpression, ProgramStatement, ProgramType, Proposition, PureFactContext,
    ResourceContext, ResourceFact, SymbolicMemory, UndefinedBehavior, int32,
    prove_symbolic_program_function_execution,
};
use click::languages::cpp::{
    CppBinaryOperator, CppExceptionBehavior, CppExpression, CppInitializer, CppStatement, CppType,
    lower_import,
};
#[cfg(not(feature = "fast-gate"))]
use click::languages::cpp::{CppCallArgument, CppCleanup, CppFunctionKind, CppProjection};
use click::surface::{
    ProgramVerificationSession, VerifiedClaim, expand_project_claim_source_by_label,
    expand_project_tactic_source_at, project_smart_tactic_source_sites,
    project_tactic_source_position, verify_program_prepared_project,
};

#[test]
// A widening helper-result initializer qualifies the object, not the scalar conversion value.
fn readonly_scalar_initialization_checks_converted_helper_results() {
    let project = Project::with_fixture(
        "readonly_wide.cpp",
        "probe",
        "int seven() noexcept { return 7; } unsigned long probe() noexcept { const unsigned long result = seven(); return result; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_first_claim_certificate(
        &project,
        &import,
        r#"verifying "readonly_wide.cpp";
int32 seven() { ensures result == 7; }
uint64 probe() { ensures result == 7u64; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
// Const scalar construction and constexpr storage must survive offline importing and alias reads.
fn readonly_scalar_initialization_keeps_cpp_object_identity() {
    check_readonly_scalar_initialization(false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: readonly scalar expanded and retained proof rechecks"]
fn readonly_scalar_initialization_expands_and_retains_offline() {
    check_readonly_scalar_initialization(true);
}

#[test]
// Const/constexpr scalar initializers must not substitute runtime constant-evaluation context.
fn readonly_scalar_initialization_refuses_context_sensitive_helpers() {
    for qualifier in ["const", "constexpr"] {
        let source = format!(
            "constexpr int choice() noexcept {{ if (__builtin_is_constant_evaluated()) return 1; return 2; }} int probe() noexcept {{ {qualifier} int extent = choice(); return extent; }}"
        );
        let project = Project::with_fixture("context.cpp", "probe", &source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("context-independent callees"), "{error}");
    }
}

fn check_readonly_scalar_initialization(tools: bool) {
    let project = Project::with_fixture(
        "readonly.cpp",
        "probe",
        "int seven() noexcept { return 7; } int read(const int& value) noexcept { return value; } int probe() noexcept { const int first = seven(); constexpr unsigned long extent = 4; const int& same = first; return read(same) + static_cast<int>(extent); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "readonly.cpp";
int32 seven() { ensures result == 7; }
int32 read(const int32& value) { views value; ensures result == value; }
int32 probe() { ensures result == 11; }
"#;
    check_arithmetic_sidecar_with_tools(&project, &import, proof, tools);
    if tools {
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
        let expanded = expand_project_claim_source_by_label(
            &parsed,
            &ProgramInputs::program(&import),
            "probe.ensures_0",
        )
        .unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import).unwrap();
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            "probe.ensures_0",
            0,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
        use sha2::{Digest, Sha256};
        let original_artifact = fs::read(project.artifact()).unwrap();
        let original_lock = fs::read(project.lock()).unwrap();
        for mutation in 0..2 {
            let mut artifact: serde_json::Value =
                serde_json::from_slice(&original_artifact).unwrap();
            if mutation == 0 {
                artifact["functions"][0]["body"][0]["initializer"] =
                    serde_json::json!({"kind":"uninitialized"});
            } else {
                let declaration = &mut artifact["functions"][0]["body"][1];
                let ty = declaration["initializer"]["value"]["value_type"].clone();
                let span = declaration["span"].clone();
                declaration["initializer"]["value"] = serde_json::json!({
                    "kind":"integral_cast", "value_type":ty, "span":span,
                    "value":{"kind":"runtime_constant_evaluation", "value_type":{"kind":"boolean","bits":8,"is_const":false}, "span":span}
                });
            }
            let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
            let mut lock: serde_json::Value = serde_json::from_slice(&original_lock).unwrap();
            lock_source_mut(&mut lock)["artifact"]["sha256"] =
                format!("{:x}", Sha256::digest(&bytes)).into();
            lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
            fs::write(project.artifact(), bytes).unwrap();
            fs::write(project.lock(), serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
            let error = load_import(&project.config()).unwrap_err();
            assert!(
                error.contains("require an initializer")
                    || error.contains("constant-evaluation context"),
                "{error}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
// A by-value descriptor copy owns only its fields, and still aliases its backing allocation.
fn trivial_record_parameter_copy_keeps_caller_fields_and_shared_backing() {
    check_trivial_record_parameter_copy(false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: expanded and retained by-value record proof rechecks"]
fn trivial_record_parameter_copy_expands_and_retains_offline() {
    check_trivial_record_parameter_copy(true);
}

#[test]
// A by-value boundary must not erase a user copy body, a move, or prvalue construction.
fn trivial_record_parameter_copy_refuses_nontrivial_move_and_prvalue_arguments() {
    for source in [
        "struct View { int size; View(const View& v) noexcept : size(v.size) {} }; int probe(View value) noexcept { return value.size; }",
        "struct View { int size; }; int take(View v) noexcept { return v.size; } int probe(View& v) noexcept { return take(static_cast<View&&>(v)); }",
        "struct View { int size; }; int take(View v) noexcept { return v.size; } int probe() noexcept { return take(View{7}); }",
    ] {
        let project = Project::with_fixture("copy.cpp", "probe", source);
        assert!(refresh_import(&project.config()).is_err());
    }
}

fn opaque_record_copy_fixture(source: &str) -> (Project, click::languages::cpp::PreparedCppImport) {
    let mut project = Project::with_fixture("opaque_copy.cpp", "probe", source);
    fs::write(
        project.directory.join("view.hpp"),
        "struct View { private: unsigned long hidden; public: View(const View&) noexcept = default; };",
    )
    .unwrap();
    project.dependencies.push("view.hpp".into());
    let mut arguments = project.compilation_arguments();
    arguments.splice(1..1, ["-isystem".into(), ".".into()]);
    project.write_compilation_database_commands(&[arguments]);
    project.write_config("probe");
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();

    (project, import)
}

const OPAQUE_VIEW_COPY_CONTRACT: &str = r#"verifying "opaque_copy.cpp";
abstract resource view_state(p: uint8*) {
    field data: int32*;
    field count: uint64;
}
extern View::View(const struct View& source) {
    owns original: view_state(&source as (uint8*));
    produces copied: view_state(this as (uint8*));
    ensures original.data == old(original.data);
    ensures original.count == old(original.count);
    ensures copied.data == original.data;
    ensures copied.count == original.count;
}"#;

const OPAQUE_VIEW_COPY_CALLER: &str = r#"
uint64 probe(const struct View& source) {
    owns original: view_state(&source as (uint8*));
    ensures original.data == old(original.data);
    ensures original.count == old(original.count);
    ensures result == old(original.count);
} by {
    step();
    let { copied: parameter_state } = step(View::View, { original: original });
    step();
    step(take_count, { copied: parameter_state });
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: opaque by-value parameter proof, replay, and refusal controls"]
fn opaque_record_copy_constructs_the_actual_by_value_parameter() {
    let (project, import) = opaque_record_copy_fixture(
        r#"#include <view.hpp>
unsigned long take_count(View parameter) noexcept;
unsigned long probe(const View& source) noexcept {
    return take_count(source);
}
"#,
    );
    let proof = format!(
        r#"{OPAQUE_VIEW_COPY_CONTRACT}
extern uint64 take_count(struct View parameter) {{
    consumes copied: view_state(&parameter as (uint8*));
    ensures result == old(copied.count);
}}
{OPAQUE_VIEW_COPY_CALLER}"#
    );

    let path = project.directory.join("opaque_copy.click");
    fs::write(&path, &proof).unwrap();
    let parsed = read_click_project(&path, &proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap_or_else(|error| panic!("{}", error.report()));
    click::surface::without_implicit_solve(|| {
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import)
    })
    .unwrap_or_else(|error| panic!("{}", error.report()));

    for (changed, refusal) in [
        (
            proof.replace(
                "step(take_count, { copied: parameter_state })",
                "step(take_count, { copied: original })",
            ),
            "named resource instance does not match",
        ),
        (
            proof.replace(
                "    consumes copied: view_state(&parameter as (uint8*));",
                "    owns copied: view_state(&parameter as (uint8*));",
            ),
            "at the end of the full expression",
        ),
    ] {
        let parsed = read_click_project(&path, &changed).unwrap();
        let error = verify_program_prepared_project(&parsed, &import)
            .expect_err("the unchecked opaque copy must fail");
        assert!(error.message().contains(refusal), "{}", error.report());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: verified callee and opaque record copy proof replay"]
fn opaque_by_value_parameter_keeps_its_contract_resource_in_the_body() {
    let (project, import) = opaque_record_copy_fixture(
        r#"#include <view.hpp>
unsigned long read_count(const View& view) noexcept;
unsigned long take_count(View parameter) noexcept {
    return read_count(parameter);
}
unsigned long probe(const View& source) noexcept {
    return take_count(source);
}
"#,
    );
    let callee = r#"
extern uint64 read_count(const struct View& view) {
    consumes copied: view_state(&view as (uint8*));
    ensures result == old(copied.count);
}
uint64 take_count(struct View parameter) {
    consumes copied: view_state(&parameter as (uint8*));
    ensures result == old(copied.count);
} by {
    step(read_count, { copied: copied });
}
"#;
    let proof = format!("{OPAQUE_VIEW_COPY_CONTRACT}{callee}{OPAQUE_VIEW_COPY_CALLER}");
    let path = project.directory.join("opaque_copy.click");
    fs::write(&path, &proof).unwrap();
    let parsed = read_click_project(&path, &proof).unwrap();
    let inputs = ProgramInputs::program(&import);
    let expanded = expand_project_claim_source_by_label(&parsed, &inputs, "take_count.contract")
        .unwrap_or_else(|error| panic!("{}", error.report()));
    let parsed = parsed.with_entry_source(expanded);
    let expanded = expand_project_claim_source_by_label(&parsed, &inputs, "probe.contract")
        .unwrap_or_else(|error| panic!("{}", error.report()));
    click::surface::without_implicit_solve(|| {
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import)
    })
    .unwrap_or_else(|error| panic!("{}", error.report()));
}

fn check_trivial_record_parameter_copy(tools: bool) {
    let project = Project::with_fixture(
        "copy.cpp",
        "probe",
        "struct View { int* data; int size; }; int change(View value) noexcept { value.size = 7; *value.data = 9; return value.size; } int probe(View& input) noexcept { int result = change(input); return input.size + result + *input.data; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof_source = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/cpp-verification/native-interface/descriptor-copy.click"),
    )
    .unwrap();
    let proof = proof_source.as_str();
    if tools {
        fs::write(project.directory.join("arithmetic.click"), proof).unwrap();
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
        // One ordinary baseline supplies the certificates and the retained
        // environment. Do not run the tactic-level round trip as well.
        let (session, verified) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let expanded = click::surface::expand_verified_function_claim_source_by_label(
            proof,
            &verified,
            "probe.contract",
        )
        .unwrap()
        .unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            "probe.contract",
            0,
        )
        .unwrap();
        click::surface::without_implicit_solve(|| {
            session.verify_at_project(&expanded, position.line, position.column)
        })
        .unwrap();
        // Expand the earlier callee after the later caller, keeping the
        // original certificate positions valid. Finish printing before the
        // independent cold check resets the kernel tables.
        let expanded = click::surface::expand_verified_function_claim_source_by_label(
            &expanded,
            &verified,
            "change.contract",
        )
        .unwrap()
        .unwrap();
        drop(session);
        let rewritten = parsed.with_entry_source(expanded);
        assert!(
            project_smart_tactic_source_sites(&rewritten, &ProgramInputs::program(&import))
                .unwrap()
                .is_empty()
        );
        click::surface::without_implicit_solve(|| {
            verify_program_prepared_project(&rewritten, &import)
        })
        .unwrap();
    } else {
        check_arithmetic_sidecar_with_tools(&project, &import, proof, false);
    }
    let invalid = proof.replace("owns input.data[0..1];", "views input.data[0..1];");
    fs::write(project.directory.join("invalid.click"), &invalid).unwrap();
    assert!(
        verify_program_prepared_project(
            &read_click_project(&project.directory.join("invalid.click"), &invalid).unwrap(),
            &import
        )
        .is_err()
    );
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    assert_eq!(
        artifact["functions"][0]["body"][0]["initializer"]["arguments"][0]["kind"],
        "record_copy"
    );
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        let argument = &mut forged["functions"][0]["body"][0]["initializer"]["arguments"][0];
        match mutation {
            0 => {
                argument["kind"] = "reference".into();
                argument.as_object_mut().unwrap().remove("value_type");
                argument.as_object_mut().unwrap().remove("span");
            }
            1 => argument["value_type"]["declaration_id"] = "c:@S@Other".into(),
            2 => argument["place"]["declaration_id"] = "expired_local".into(),
            3 => argument["span"]["file"] = "unlocked.cpp".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        use sha2::{Digest, Sha256};
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn trivial_record_return_preserves_nested_descriptor_values_offline() {
    let project = Project::with_fixture(
        "copy.cpp",
        "copy",
        "struct Extent { unsigned long size; }; struct View { int* data; Extent extent; }; View copy(const View& input) noexcept { return input; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[0],
        CppStatement::ReturnRecord { .. }
    ));
    let proof = r#"verifying "copy.cpp";
struct View copy(const struct View& input) {
 views input.data;
 views input.extent.size;
 ensures result.data == input.data;
 ensures result.extent.size == input.extent.size;
 ensures input.data == old(input.data);
 ensures input.extent.size == old(input.extent.size);
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let whole = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &whole,
        &ProgramInputs::program(&import),
        "copy.contract",
    )
    .unwrap();
    verify_program_prepared_project(&whole.with_entry_source(expanded), &import).unwrap();
    for invalid in [
        proof.replace(" views input.data;", ""),
        proof.replace(" views input.extent.size;", ""),
        proof.replace(
            "result.extent.size == input.extent.size",
            "result.extent.size == input.extent.size + 1u64",
        ),
        proof.replace("result.data == input.data", "result.data != input.data"),
    ] {
        let path = project.directory.join("invalid.click");
        fs::write(&path, &invalid).unwrap();
        let parsed = read_click_project(&path, &invalid).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
    use sha2::{Digest, Sha256};
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        match mutation {
            0 => forged["functions"][0]["body"][0]["value_type"]["name"] = "Other".into(),
            1 => {
                forged["functions"][0]["body"][0]["source"]["declaration_id"] =
                    "expired_local".into()
            }
            2 => forged["functions"][0]["body"][0]["span"]["file"] = "unlocked.cpp".into(),
            3 => {
                let record = artifact["records"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|record| record["name"] == "View")
                    .unwrap();
                let field = &record["fields"][0];
                forged["functions"][0]["body"][0]["source"]["projections"] = serde_json::json!([{
                    "record_declaration_id":record["declaration_id"], "declaration_id":field["declaration_id"], "name":field["name"], "span":field["span"]
                }]);
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        let error = load_import(&project.config()).unwrap_err();
        if mutation == 3 {
            assert!(
                error.contains("same nominal source and result record"),
                "{error}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn projected_trivial_record_return_verifies_without_copying_siblings() {
    let project = Project::with_fixture(
        "copy.cpp",
        "copy",
        "struct Extent { unsigned long size; }; struct View { int* data; Extent extent; }; Extent copy(const View& input) noexcept { return input.extent; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_first_claim_certificate(
        &project,
        &import,
        r#"verifying "copy.cpp";
struct Extent copy(const struct View& input) {
 views input.extent.size;
 ensures result.size == input.extent.size;
 ensures input.extent.size == old(input.extent.size);
}
"#,
    );
}

#[test]
fn record_return_refuses_nontrivial_copy_move_and_prvalue_construction() {
    for source in [
        "struct View { int value; View(const View& other) noexcept : value(other.value + 1) {} }; View copy(const View& input) noexcept { return input; }",
        "struct View { int value; View(View&&) noexcept = default; }; View copy(View& input) noexcept { return static_cast<View&&>(input); }",
        "struct View { int value; }; View copy(const View& input) noexcept { return View{input.value}; }",
    ] {
        let project = Project::with_fixture("copy.cpp", "copy", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("record return requires")
                || error.contains("must remain trivially copyable"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn constructor_destination_preserves_pointer_to_its_own_field_offline() {
    let project = Project::with_fixture(
        "identity.cpp",
        "probe",
        r#"
struct Node {
    int* self;
    int value;
    explicit Node(int input) noexcept : self(&value), value(input) {}
};
int probe(int input) noexcept {
    Node node(input);
    return *node.self;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "identity.cpp";
Node::Node(int32 input) {
 owns this->value;
 owns this->self;
 ensures this->value == input;
 ensures this->self == &this->value;
}
int32 probe(int32 input) {
 ensures result == input;
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    for label in ["Node::Node.contract", "probe.ensures_0"] {
        let expanded =
            expand_project_claim_source_by_label(&parsed, &ProgramInputs::program(&import), label)
                .unwrap();
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
    }
    for invalid in [
        proof.replace("this->self == &this->value", "this->self != &this->value"),
        proof.replace("result == input", "result == input + 1"),
        proof.replace(" owns this->value;", ""),
    ] {
        let path = project.directory.join("invalid.click");
        fs::write(&path, &invalid).unwrap();
        let parsed = read_click_project(&path, &invalid).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn record_field_address_preserves_const_qualification_offline() {
    let project = Project::with_fixture(
        "address.cpp",
        "probe",
        "struct Node { int value; }; const int& probe(const Node& input) noexcept { return *(&input.value); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_first_claim_certificate(
        &project,
        &import,
        r#"verifying "address.cpp";
const int32& probe(const struct Node& input) {
 views input.value;
 ensures &result == &input.value;
 ensures result == input.value;
}
"#,
    );
    use sha2::{Digest, Sha256};
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    artifact["functions"][0]["body"][0]["value"]["address"]["value_type"]["pointee"]["is_const"] =
        false.into();
    let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    lock_source_mut(&mut lock)["artifact"]["sha256"] =
        format!("{:x}", Sha256::digest(&bytes)).into();
    lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
    fs::write(project.artifact(), bytes).unwrap();
    fs::write(project.lock(), serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(
        error.contains("field address changed type or const qualification"),
        "{error}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn record_copy_keeps_self_pointer_value_without_rebasing_it() {
    let project = Project::with_fixture(
        "copy.cpp",
        "probe",
        "struct Node { int* self; int value; }; int* probe(Node& target, const Node& source) noexcept { target = source; return target.self; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "copy.cpp";
int32* probe(struct Node& target, const struct Node& source) {
 owns target.self;
 owns target.value;
 views source.self;
 views source.value;
 requires source.self == &source.value;
 ensures target.self == source.self;
 ensures result == &source.value;
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let invalid = proof.replace("result == &source.value", "result == &target.value");
    let path = project.directory.join("invalid.click");
    fs::write(&path, &invalid).unwrap();
    let parsed = read_click_project(&path, &invalid).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

const SOURCE: &str = include_str!("../examples/basic-cpp/increment.cpp");

#[test]
fn trivial_record_copy_assignment_preserves_self_and_projected_values() {
    let project = Project::with_fixture(
        "copy.cpp",
        "probe",
        "struct Extent { unsigned long size; }; struct View { int* data; Extent extent; }; int probe(View& target, const View& source) { target.extent = source.extent; target = target; return 0; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_profile("probe", "copy.cpp", true);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[0],
        CppStatement::TrivialCopy { .. }
    ));
    let source = r#"verifying "copy.cpp";
int32 probe(struct View& target, const struct View& source) {
 owns target.data;
 owns target.extent.size;
 views source.extent.size;
 requires separate(memory((&target as (uint8*))[0..16]), memory(source.extent.size));
 ensures target.data == old(target.data);
 ensures target.extent.size == source.extent.size;
 ensures source.extent.size == old(source.extent.size);
 ensures result == 0;
} by {
 step() by { close(); }
 step() by { close(); }
}
"#;
    let path = project.directory.join("copy.click");
    fs::write(&path, source).unwrap();
    let click_project = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&click_project, &import).unwrap();
    use sha2::{Digest, Sha256};
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..3 {
        let mut forged = artifact.clone();
        match mutation {
            0 => {
                forged["functions"][0]["parameters"][0]["value_type"]["pointee"]["is_const"] =
                    true.into()
            }
            1 => forged["functions"][0]["body"][0]["source"]["projections"] = serde_json::json!([]),
            2 => forged["functions"][0]["body"][0]["span"]["file"] = "unlocked.cpp".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn record_assignment_refuses_nontrivial_copy_and_move_bodies() {
    for source in [
        "struct View { int value; View& operator=(const View& other) noexcept { value = other.value + 1; return *this; } }; int probe(View& target, const View& source) { target = source; return 0; }",
        "struct View { int value; View& operator=(View&&) noexcept = default; }; int probe(View& target, View& source) { target = static_cast<View&&>(source); return 0; }",
    ] {
        let project = Project::with_fixture("copy.cpp", "probe", source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_profile("probe", "copy.cpp", true);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("requires a trivial copy assignment")
                || error.contains("must remain trivially copyable"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }
}

const SIDECAR: &str = include_str!("../examples/basic-cpp/increment.click");
const BRANCH_SOURCE: &str = include_str!("fixtures/cpp-verification/branch-return/choose.cpp");
const BRANCH_SIDECAR: &str = include_str!("fixtures/cpp-verification/branch-return/choose.click");
const CONST_REFERENCE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/const-reference-alias/write_then_read.cpp");
const CONST_REFERENCE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/const-reference-alias/write_then_read.click");
const DIRECT_CALL_SOURCE: &str =
    include_str!("fixtures/cpp-verification/direct-call/call_set_seven.cpp");
const DIRECT_CALL_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/direct-call/call_set_seven.click");
const SCALAR_LOCAL_SOURCE: &str =
    include_str!("fixtures/cpp-verification/scalar-local/relay_value.cpp");
const SCALAR_LOCAL_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/scalar-local/relay_value.click");
const POINTER_SOURCE: &str = include_str!("fixtures/cpp-verification/pointer/bump_reference.cpp");
const POINTER_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/pointer/bump_reference.click");
const STRUCT_MEMBER_SOURCE: &str =
    include_str!("fixtures/cpp-verification/struct-member/stage_restore.cpp");
const STRUCT_MEMBER_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/struct-member/stage_restore.click");
const LOCAL_AGGREGATE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/local-aggregate/stage_restore.cpp");
const LOCAL_AGGREGATE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/local-aggregate/stage_restore.click");
const CONSTRUCTOR_LOCAL_SOURCE: &str =
    include_str!("fixtures/cpp-verification/constructor-local/capture.cpp");
const CONSTRUCTOR_LOCAL_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constructor-local/capture.click");
const TERMINAL_DESTRUCTOR_SOURCE: &str =
    include_str!("fixtures/cpp-verification/terminal-destructor/capture.cpp");
const TERMINAL_DESTRUCTOR_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/terminal-destructor/capture.click");
const EARLY_RETURN_DESTRUCTOR_SOURCE: &str = include_str!("../examples/basic-cpp/with_restore.cpp");
const EARLY_RETURN_DESTRUCTOR_SIDECAR: &str =
    include_str!("../examples/basic-cpp/with_restore.click");
const RESTORE_CALLER_SOURCE: &str = include_str!("../examples/basic-cpp/with_restore_caller.cpp");
const RESTORE_CALLER_SIDECAR: &str =
    include_str!("../examples/basic-cpp/with_restore_caller.click");
const REVERSE_DESTRUCTOR_SOURCE: &str =
    include_str!("fixtures/cpp-verification/reverse-destructor-order/restore_twice.cpp");
const REVERSE_DESTRUCTOR_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/reverse-destructor-order/restore_twice.click");
const NESTED_SCOPE_DESTRUCTOR_SOURCE: &str =
    include_str!("fixtures/cpp-verification/nested-scope-destructor/scoped_restore.cpp");
const NESTED_SCOPE_DESTRUCTOR_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/nested-scope-destructor/scoped_restore.click");
const SIBLING_SCOPE_DESTRUCTORS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/sibling-scope-destructors/sibling_restore.cpp");
const SIBLING_SCOPE_DESTRUCTORS_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/sibling-scope-destructors/sibling_restore.click");
const OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/overlapping-scope-destructors/overlap_restore.cpp");
const OVERLAPPING_SCOPE_DESTRUCTORS_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/overlapping-scope-destructors/overlap_restore.click");
const CONDITIONAL_CONSTRUCTION_SOURCE: &str =
    include_str!("fixtures/cpp-verification/conditional-construction/conditional_restore.cpp");
const CONDITIONAL_CONSTRUCTION_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/conditional-construction/conditional_restore.click");
const INT64_PREDICATE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/int64-predicate/money_nonnegative.cpp");
const INT64_PREDICATE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/int64-predicate/money_nonnegative.click");
const CONSTEXPR_COIN_SOURCE: &str =
    include_str!("fixtures/cpp-verification/constexpr-coin/at_least_one_coin.cpp");
const CONSTEXPR_COIN_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-coin/at_least_one_coin.click");
const CONSTEXPR_COIN_CSTDINT: &str =
    include_str!("fixtures/cpp-verification/constexpr-coin/cstdint");
const CONSTEXPR_MAX_MONEY_SOURCE: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/at_least_max_money.cpp");
const CONSTEXPR_MAX_MONEY_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/at_least_max_money.click");
const CONSTEXPR_MAX_MONEY_LE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/at_most_max_money.click");
const CONSTEXPR_MAX_MONEY_RANGE_SIDECAR: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/money_range.click");
const CONSTEXPR_MAX_MONEY_CSTDINT: &str =
    include_str!("fixtures/cpp-verification/constexpr-max-money/cstdint");
const ONE_GUARD_UNWIND_MDTEST: &str = include_str!("../mdtests/cpp_one_guard_unwind.md");
const GUARD_BEFORE_SECOND_MDTEST: &str =
    include_str!("../mdtests/cpp_guard_unwind_before_second.md");

#[path = "support/cpp_description.rs"]
mod cpp_description;
use cpp_description::{
    load_import, lock_description, lock_section, lock_source_mut, refresh_import,
};
#[cfg(not(feature = "fast-gate"))]
use cpp_description::{unit_digest, unit_entry_mut};

struct Project {
    directory: PathBuf,
    exporter: PathBuf,
    source_name: String,
    dependencies: Vec<String>,
}

impl Project {
    fn new() -> Self {
        Self::with_fixture("increment.cpp", "increment", SOURCE)
    }

    fn branch_return() -> Self {
        Self::with_fixture("choose.cpp", "choose", BRANCH_SOURCE)
    }

    fn const_reference_alias() -> Self {
        Self::with_fixture(
            "write_then_read.cpp",
            "write_then_read",
            CONST_REFERENCE_SOURCE,
        )
    }

    fn direct_call() -> Self {
        Self::with_fixture("call_set_seven.cpp", "call_set_seven", DIRECT_CALL_SOURCE)
    }

    fn scalar_local() -> Self {
        Self::with_fixture("relay_value.cpp", "relay_value", SCALAR_LOCAL_SOURCE)
    }

    fn pointer() -> Self {
        Self::with_fixture("bump_reference.cpp", "bump_reference", POINTER_SOURCE)
    }

    fn struct_member() -> Self {
        Self::with_fixture("stage_restore.cpp", "stage_restore", STRUCT_MEMBER_SOURCE)
    }

    fn local_aggregate() -> Self {
        Self::with_fixture("stage_restore.cpp", "stage_restore", LOCAL_AGGREGATE_SOURCE)
    }

    fn constructor_local() -> Self {
        Self::with_fixture("capture.cpp", "capture", CONSTRUCTOR_LOCAL_SOURCE)
    }

    fn terminal_destructor() -> Self {
        Self::with_fixture("capture.cpp", "capture", TERMINAL_DESTRUCTOR_SOURCE)
    }

    fn early_return_destructor() -> Self {
        Self::with_fixture(
            "with_restore.cpp",
            "with_restore",
            EARLY_RETURN_DESTRUCTOR_SOURCE,
        )
    }

    fn restore_caller() -> Self {
        Self::with_fixture(
            "with_restore_caller.cpp",
            "call_with_restore",
            RESTORE_CALLER_SOURCE,
        )
    }

    fn reverse_destructor_order() -> Self {
        Self::with_fixture(
            "restore_twice.cpp",
            "restore_twice",
            REVERSE_DESTRUCTOR_SOURCE,
        )
    }

    fn nested_scope_destructor() -> Self {
        Self::with_fixture(
            "scoped_restore.cpp",
            "scoped_restore",
            NESTED_SCOPE_DESTRUCTOR_SOURCE,
        )
    }

    fn sibling_scope_destructors() -> Self {
        Self::with_fixture(
            "sibling_restore.cpp",
            "sibling_restore",
            SIBLING_SCOPE_DESTRUCTORS_SOURCE,
        )
    }

    fn overlapping_scope_destructors() -> Self {
        Self::with_fixture(
            "overlap_restore.cpp",
            "overlap_restore",
            OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE,
        )
    }

    fn conditional_construction() -> Self {
        Self::with_fixture(
            "conditional_restore.cpp",
            "conditional_restore",
            CONDITIONAL_CONSTRUCTION_SOURCE,
        )
    }

    fn header_function() -> Self {
        let project = Self::with_fixture(
            "driver.cpp",
            "header_increment",
            "#include \"selected.h\"\n",
        );
        fs::write(
            project.logical_header(),
            "inline int header_increment(int& value) noexcept {\n    value = value + 1;\n    return value;\n}\n",
        )
        .unwrap();
        project.write_config_with_logical_source("header_increment", "selected.h");
        project
    }

    fn exception_enabled_header_function() -> Self {
        let project = Self::header_function();
        fs::write(
            project.logical_header(),
            "inline int header_increment(int& value) {\n    value = value + 1;\n    return value;\n}\n",
        )
        .unwrap();
        project.write_exception_enabled_compilation_database();
        project.write_config_with_profile("header_increment", "selected.h", true);
        project
    }

    fn int64_predicate() -> Self {
        let project = Self::with_fixture(
            "money_nonnegative.cpp",
            "money_nonnegative",
            INT64_PREDICATE_SOURCE,
        );
        project.write_exception_enabled_compilation_database();
        project.write_config_with_profile("money_nonnegative", "money_nonnegative.cpp", true);
        project
    }

    fn constexpr_coin() -> Self {
        let mut project = Self::with_fixture(
            "at_least_one_coin.cpp",
            "at_least_one_coin",
            CONSTEXPR_COIN_SOURCE,
        );
        fs::write(project.directory.join("cstdint"), CONSTEXPR_COIN_CSTDINT).unwrap();
        project.dependencies.push("cstdint".into());
        project.write_exception_enabled_compilation_database_with_local_include();
        project.write_config_with_profile("at_least_one_coin", "at_least_one_coin.cpp", true);
        project
    }

    fn constexpr_max_money() -> Self {
        let mut project = Self::with_fixture(
            "at_least_max_money.cpp",
            "at_least_max_money",
            CONSTEXPR_MAX_MONEY_SOURCE,
        );
        fs::write(
            project.directory.join("cstdint"),
            CONSTEXPR_MAX_MONEY_CSTDINT,
        )
        .unwrap();
        project.dependencies.push("cstdint".into());
        project.write_exception_enabled_compilation_database_with_local_include();
        project.write_config_with_profile("at_least_max_money", "at_least_max_money.cpp", true);
        project
    }

    fn constexpr_max_money_less_equal() -> Self {
        let project = Self::constexpr_max_money();
        project.write_config_with_profile("at_most_max_money", "at_least_max_money.cpp", true);
        project
    }

    fn constexpr_max_money_range() -> Self {
        let project = Self::constexpr_max_money();
        project.write_config_with_profile("money_range", "at_least_max_money.cpp", true);
        project
    }

    fn with_fixture(source_name: &str, function: &str, source: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let directory = std::env::temp_dir().join(format!(
            "click-cpp-import-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let built_exporter = std::env::var_os("CLICK_CPP_EXPORTER")
            .map(PathBuf::from)
            .expect("scripts/check.sh supplies the pinned C++ exporter");
        let exporter = directory.join("click-cpp-exporter");
        fs::copy(&built_exporter, &exporter).expect("copy C++ exporter into isolated fixture");
        fs::write(directory.join(source_name), source).unwrap();
        let project = Self {
            directory,
            exporter,
            source_name: source_name.to_string(),
            dependencies: Vec::new(),
        };
        project.write_compilation_database();
        project.write_config(function);
        project
    }

    fn config(&self) -> PathBuf {
        self.directory.join("demo.import-description.json")
    }

    /// Locks the fixture's project with the built exporter, which survives
    /// the removal of the fixture's private copy.
    fn adopt(&self) {
        lock_description(
            &self.config(),
            std::env::var_os("CLICK_CPP_EXPORTER").map(PathBuf::from),
        )
        .expect("lock the fixture's project");
    }

    fn artifact(&self) -> PathBuf {
        cpp_description::artifact(&self.config())
    }

    /// The size of the artifact as loading decodes it: the stored artifact
    /// names the fixture's roots by their labels, and loading replaces each
    /// label by the root's location.
    fn loaded_artifact_bytes(&self) -> usize {
        let root = fs::canonicalize(&self.directory).unwrap();
        let root = root.to_str().unwrap();
        fs::read_to_string(self.artifact())
            .unwrap()
            .replace("\"$unit", &format!("\"{root}"))
            .replace("\"$project", &format!("\"{root}"))
            .replace("\"$clang-resource", "\"/click-pinned-clang-resource")
            .len()
    }

    fn lock(&self) -> PathBuf {
        self.directory.join(click::project::LOCK_NAME)
    }

    fn source(&self) -> PathBuf {
        self.directory.join(&self.source_name)
    }

    fn logical_header(&self) -> PathBuf {
        self.directory.join("selected.h")
    }

    fn compilation_database(&self) -> PathBuf {
        self.directory.join("compile_commands.json")
    }

    fn compilation_arguments(&self) -> Vec<String> {
        [
            "clang++",
            "-x",
            "c++",
            "-std=c++20",
            "--target=x86_64-unknown-linux-gnu",
            "-fno-exceptions",
            "-fno-rtti",
            "-funsigned-char",
            "-ffreestanding",
            "-nostdinc",
            "-nostdinc++",
            "-Wno-reorder-ctor",
            "-c",
            &self.source_name,
            "-o",
            "fixture.o",
        ]
        .into_iter()
        .map(str::to_string)
        .collect()
    }

    /// The command Click synthesizes for the unit: the fixture's command at
    /// `-O0`, the level of a description whose command names none, writing
    /// the object beside the translation unit.
    fn synthesized_arguments(&self) -> Vec<String> {
        let mut arguments = self.compilation_arguments();
        *arguments.last_mut().unwrap() = format!("{}.o", self.source_name);
        let after_rtti = arguments.iter().position(|a| a == "-fno-rtti").unwrap() + 1;
        arguments.insert(after_rtti, "-O0".to_string());
        arguments
    }

    fn exception_enabled_compilation_arguments(&self) -> Vec<String> {
        self.compilation_arguments()
            .into_iter()
            .map(|argument| {
                if argument == "-fno-exceptions" {
                    "-fexceptions".into()
                } else {
                    argument
                }
            })
            .collect()
    }

    fn write_compilation_database(&self) {
        self.write_compilation_database_commands(&[self.compilation_arguments()]);
    }

    fn write_exception_enabled_compilation_database(&self) {
        self.write_compilation_database_commands(&[self.exception_enabled_compilation_arguments()]);
    }

    fn write_exception_enabled_compilation_database_with_local_include(&self) {
        let mut arguments = self.exception_enabled_compilation_arguments();
        let compile = arguments
            .iter()
            .position(|argument| argument == "-c")
            .expect("fixture compilation command has -c");
        arguments.insert(compile, "-I.".into());
        self.write_compilation_database_commands(&[arguments]);
    }

    fn write_compilation_database_commands(&self, commands: &[Vec<String>]) {
        let database = commands
            .iter()
            .map(|arguments| {
                serde_json::json!({
                    "directory": self.directory,
                    "file": self.source_name,
                    "arguments": arguments,
                    "output": "fixture.o"
                })
            })
            .collect::<Vec<_>>();
        let mut bytes = serde_json::to_vec_pretty(&database).unwrap();
        bytes.push(b'\n');
        fs::write(self.compilation_database(), bytes).unwrap();
    }

    fn write_config(&self, function: &str) {
        self.write_config_with_logical_source(function, &self.source_name);
    }

    fn write_config_with_logical_source(&self, function: &str, logical_source: &str) {
        self.write_config_with_profile(function, logical_source, false);
    }

    fn write_config_with_profile(&self, function: &str, logical_source: &str, exceptions: bool) {
        self.write_config_with_exception_behavior(
            function,
            logical_source,
            exceptions,
            "normal_only",
        );
    }

    fn write_config_with_templates(&self, function: &str, templates: &[&str]) {
        self.write_config(function);
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(self.config()).unwrap()).unwrap();
        config["templates"] = serde_json::json!(templates);
        fs::write(self.config(), serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    }

    fn write_config_with_exception_behavior(
        &self,
        function: &str,
        logical_source: &str,
        exceptions: bool,
        exception_behavior: &str,
    ) {
        let config = serde_json::json!({
            "schema": 6,
            "language": "c++",
            "standard": "c++20",
            "target": "x86_64-unknown-linux-gnu",
            "exceptions": exceptions,
            "exception_behavior": exception_behavior,
            "rtti": false,
            "exporter": self.exporter,
            "compilation_database": "compile_commands.json",
            "working_directory": ".",
            "source": &self.source_name,
            "logical_source": logical_source,
            "dependencies": &self.dependencies,
            "function": function,
            "artifact": format!("{}.click-cpp.json", self.source_name)
        });
        let mut bytes = serde_json::to_vec_pretty(&config).unwrap();
        bytes.push(b'\n');
        fs::write(self.config(), bytes).unwrap();
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn literal_false_do_wrappers_execute_once_offline() {
    for condition in ["false", "0"] {
        let project = Project::with_fixture(
            "once.cpp",
            "probe",
            &format!(
                "int probe(int& value) noexcept {{ do {{ value = 7; }} while ({condition}); return value; }}"
            ),
        );
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        check_first_claim_certificate(
            &project,
            &import,
            r#"verifying "once.cpp";
int32 probe(int32& value) {
 owns value;
 ensures value == 7;
 ensures result == 7;
}
"#,
        );
    }
}

#[test]
fn do_wrappers_refuse_repetition_runtime_conditions_and_control_transfers() {
    for (body, condition, expected) in [
        ("value = 7;", "true", "literal false condition"),
        ("value = 7;", "value == 0", "literal false condition"),
        ("break;", "false", "unsupported statement"),
        ("continue;", "false", "unsupported statement"),
    ] {
        let project = Project::with_fixture(
            "once.cpp",
            "probe",
            &format!(
                "int probe(int& value) noexcept {{ do {{ {body} }} while ({condition}); return value; }}"
            ),
        );
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn while_loops_refuse_control_transfers_call_conditions_and_record_locals() {
    for (source, expected) in [
        (
            "int probe(int n) noexcept { int i = 0; while (i < n) { break; } return i; }",
            "unsupported statement",
        ),
        (
            "int probe(int n) noexcept { int i = 0; while (i < n) { i = i + 1; continue; } return i; }",
            "unsupported statement",
        ),
        (
            "bool more(int i) noexcept { return i < 3; } int probe(int n) noexcept { int i = 0; while (more(i)) { i = i + 1; } return i; }",
            "a C++ while condition is an expression, not a call",
        ),
        (
            "struct P { int x; }; int probe(int n) noexcept { int i = 0; while (i < n) { P p{i + 1}; i = p.x; } return i; }",
            "a C++ loop body declares only scalar and pointer locals",
        ),
        (
            "int probe(int n) noexcept { int i = n; while (int j = i) { i = j - 1; } return i; }",
            "cannot declare a condition variable",
        ),
    ] {
        let project = Project::with_fixture("loop.cpp", "probe", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(expected), "{source}: {error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn observer_contracts_reject_writes_even_when_the_value_is_restored() {
    let project = Project::with_fixture(
        "observer.cpp",
        "probe",
        "int probe(int& value) noexcept { int saved = value; value = 7; value = saved; return value; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "observer.cpp";
int32 probe(int32& value) {
 owns value;
 ensures value == old(value);
 ensures result == old(value);
}
"#;
    let path = project.directory.join("observer.click");
    fs::write(&path, source).unwrap();
    verify_program_prepared_project(&read_click_project(&path, source).unwrap(), &import).unwrap();
    let readonly = source.replace("owns value;", "views value;");
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &readonly).unwrap(), &import)
            .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn expression_observers_preserve_symbolic_field_reads_offline() {
    let project = Project::with_fixture(
        "observe.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; unsigned long probe(const Count& count) noexcept { return count.value + count.size(); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"import click::integer;
verifying "observe.cpp";
uint64 Count::size() const {
 views this->value;
 ensures result == this->value;
}
uint64 probe(const struct Count& count) {
 views count.value;
 ensures result == integer::uint64_wrapping_add(count.value, count.value);
}
"#;
    check_selected_claim_certificate(&project, &import, source);
    let path = project.directory.join("observe.click");
    fs::write(&path, source).unwrap();
    let owning = source
        .replace("views this->value;", "owns this->value;")
        .replace("views count.value;", "owns count.value;");
    let error =
        verify_program_prepared_project(&read_click_project(&path, &owning).unwrap(), &import)
            .unwrap_err();
    assert!(
        error.message().contains("requires a read-only contract"),
        "{}",
        error.message()
    );
    for hostile in [
        source.replace("views this->value;", "owns this->value;"),
        source.replace("views count.value;", ""),
        source.replace(
            "result == integer::uint64_wrapping_add(count.value, count.value);",
            "result != integer::uint64_wrapping_add(count.value, count.value);",
        ),
    ] {
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
    use sha2::{Digest, Sha256};
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        let call = &mut forged["functions"][0]["body"][0]["value"]["right"];
        match mutation {
            0 => call["callee"]["declaration_id"] = "missing".into(),
            1 => call["value_type"]["bits"] = 32.into(),
            2 => call["span"]["file"] = "unlocked.cpp".into(),
            3 => forged["reachable_functions"][0]["declared_noexcept"] = false.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn expression_observers_normalize_nested_arguments_and_widened_results() {
    let project = Project::with_fixture(
        "observe.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; unsigned long echo(unsigned long value) noexcept { return value; } unsigned long probe(const Count& count) noexcept { return count.value + echo(count.size()); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"import click::integer;
verifying "observe.cpp";
uint64 Count::size() const { views this->value; ensures result == this->value; }
uint64 echo(uint64 value) { ensures result == value; }
uint64 probe(const struct Count& count) { views count.value; ensures result == integer::uint64_wrapping_add(count.value, count.value); }
"#,
    );
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int echo(int value) noexcept { return value; } long relay(int value) noexcept { return echo(value) + 1; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; }
int64 relay(int32 value) { requires value == 0; ensures result == 1i64; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn expression_observers_preserve_short_circuit_read_permissions() {
    for condition in ["false", "true"] {
        let project = Project::with_fixture(
            "observe.cpp",
            "probe",
            &format!(
                "struct Count {{ unsigned long value; }}; bool enabled() noexcept {{ return {condition}; }} bool read(const Count& count) noexcept {{ return count.value == 0; }} bool probe(const Count& count) noexcept {{ return enabled() && read(count); }}"
            ),
        );
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            r#"verifying "observe.cpp";
bool enabled() {{ ensures result == {condition}; }}
bool read(const struct Count& count) {{ views count.value; requires count.value == 0u64; ensures result == true; }}
bool probe(const struct Count& count) {{ ensures result == result; }}
"#
        );
        if condition == "false" {
            check_selected_claim_certificate(&project, &import, &source);
        } else {
            let path = project.directory.join("observe.click");
            fs::write(&path, &source).unwrap();
            assert!(
                verify_program_prepared_project(
                    &read_click_project(&path, &source).unwrap(),
                    &import
                )
                .is_err()
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn expression_observers_form_checked_reference_results() {
    let project = Project::with_fixture(
        "observe.cpp",
        "probe",
        "struct View { int* pointer; int* data() const noexcept { return pointer; } }; int& probe(const View& view) noexcept { return *view.data(); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "observe.cpp";
int32* View::data() const { views this->pointer; ensures result == this->pointer; }
int32& probe(const struct View& view) { views view.pointer; views view.pointer[0..1]; ensures &result == view.pointer; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let path = project.directory.join("observe.click");
    fs::write(&path, source).unwrap();
    let hostile = source.replace("views view.pointer[0..1];", "");
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn nested_reference_read_reports_the_unsupported_expression() {
    let source = "struct Byte { unsigned char value; const unsigned char& get() const noexcept { return value; } }; bool probe(const Byte& byte) noexcept { return byte.get() == 67; }";
    let project = Project::with_fixture("observe.cpp", "probe", source);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("reading a C++ call's reference result inside a larger expression"),
        "{error}"
    );
    let supported = source.replace(
        "return byte.get() == 67;",
        "const unsigned char value = byte.get(); return value == 67;",
    );
    let project = Project::with_fixture("observe.cpp", "probe", &supported);
    refresh_import(&project.config()).unwrap();
}

#[test]
fn expression_observers_refuse_mutation_despite_a_matching_native_signature() {
    let project = Project::with_fixture(
        "observe.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() noexcept { value = 5; return value; } }; unsigned long probe(Count& count) noexcept { return count.value + count.size(); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "observe.cpp";
uint64 Count::size() {
 views this->value;
 ensures result == 5u64;
}
uint64 probe(struct Count& count) {
 views count.value;
 ensures result == count.value + 5u64;
}
"#;
    let path = project.directory.join("observe.click");
    fs::write(&path, source).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, source).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn declared_macro_definitions_keep_expansion_locations_and_locks_offline() {
    let mut project = Project::with_fixture(
        "macro.cpp",
        "probe",
        "#include \"read.h\"\nint probe(int value) noexcept { return read(value); }",
    );
    fs::write(project.directory.join("read.h"), "#include \"check.h\"\ninline int read(int value) noexcept { CHECK(value > 0); return value; }\n").unwrap();
    let macro_body = "#define CHECK(value) do { if (__builtin_is_constant_evaluated() && !(value)) { __builtin_unreachable(); } } while (false)\n";
    fs::write(project.directory.join("check.h"), macro_body).unwrap();
    project
        .dependencies
        .extend(["check.h".into(), "read.h".into()]);
    project.write_config("probe");
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let canonical_header = project.directory.join("check.h").canonicalize().unwrap();
    assert!(
        import
            .export()
            .preprocessor_files
            .iter()
            .any(|file| file.canonical_path == canonical_header.to_string_lossy())
    );
    let sidecar = "verifying \"macro.cpp\";\nint32 read(int32 value) { ensures result == value; }\nint32 probe(int32 value) { ensures result == value; }\n";
    check_selected_claim_certificate(&project, &import, sidecar);
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let condition = &artifact["reachable_functions"][0]["body"][0]["then_branch"][0]["condition"];
    assert_eq!(condition["span"]["file"], "read.h");
    assert_eq!(condition["span"]["start_line"], 2);
    fs::write(
        project.directory.join("check.h"),
        macro_body.replace("!(value)", "(value)"),
    )
    .unwrap();
    assert!(load_import(&project.config()).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn reference_result_claim_and_solve_expansion_preserve_address_and_value_spelling() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        "int& helper(int& value) noexcept { return value; } int& probe(int& value) noexcept { return helper(value); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
int32& helper(int32& value) { views value; ensures &result == &value; ensures result == old(value); }
int32& probe(int32& value) { views value; ensures &result == &value; ensures result == old(value); }
"#;
    let path = project.directory.join("reference.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
    let position = project_tactic_source_position(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
        0,
    )
    .unwrap();
    for expanded in [
        click::surface::expand_project_claim_source_by_label(
            &parsed,
            &ProgramInputs::program(&import),
            "probe.contract",
        )
        .unwrap(),
        expand_project_tactic_source_at(
            &parsed,
            &ProgramInputs::program(&import),
            position.line,
            position.column,
        )
        .unwrap(),
    ] {
        assert!(!expanded.contains("result[0]"), "{expanded}");
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn reference_aliases_preserve_resolved_types_and_const_qualification_offline() {
    for (native_type, sidecar_type) in [("int&", "int32&"), ("const int&", "const int32&")] {
        let cpp = format!(
            "using Reference = {native_type}; Reference probe(int* data) noexcept {{ return *data; }}"
        );
        let project = Project::with_fixture("reference.cpp", "probe", &cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"reference.cpp\";\n{sidecar_type} probe(int32* data) {{ views data[0..1]; ensures &result == data; }}\n"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let path = project.directory.join("bad.click");
        let mismatched = source.replace(
            sidecar_type,
            if native_type == "int&" {
                "const int32&"
            } else {
                "int32&"
            },
        );
        fs::write(&path, &mismatched).unwrap();
        assert!(
            verify_program_prepared_project(
                &read_click_project(&path, &mismatched).unwrap(),
                &import
            )
            .is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn runtime_constant_evaluation_keeps_manifest_branch_selection_distinct_offline() {
    for (cpp, expected) in [
        (
            "bool probe() noexcept { return __builtin_is_constant_evaluated(); }",
            false,
        ),
        (
            "constexpr bool evaluated() noexcept { return __builtin_is_constant_evaluated(); } bool probe() noexcept { return evaluated(); }",
            false,
        ),
        (
            "constexpr bool evaluated() noexcept { return __builtin_is_constant_evaluated(); } bool probe() noexcept { if constexpr (evaluated()) { return true; } else { return false; } }",
            true,
        ),
        (
            "bool probe() noexcept { if (__builtin_is_constant_evaluated()) { return true; } else { return false; } }",
            false,
        ),
    ] {
        let project = Project::with_fixture("evaluation.cpp", "probe", cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let helper = if import
            .export()
            .reachable_functions
            .iter()
            .any(|function| function.name == "evaluated")
        {
            "bool evaluated() { ensures result == false; }\n"
        } else {
            ""
        };
        let source = format!(
            "verifying \"evaluation.cpp\";\n{helper}bool probe() {{ ensures result == {expected}; }}\n"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace(
            &format!("result == {expected}"),
            &format!("result == {}", !expected),
        );
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
fn boolean_primitive_artifacts_refuse_forged_types_contexts_and_locations() {
    use sha2::{Digest, Sha256};
    for cpp in [
        "bool probe() noexcept { return __builtin_is_constant_evaluated(); }",
        "bool probe(int value) noexcept { return !value; }",
    ] {
        let project = Project::with_fixture("boolean.cpp", "probe", cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        for mutation in 0..3 {
            let mut forged = artifact.clone();
            let expression = &mut forged["functions"][0]["body"][0]["value"];
            match mutation {
                0 => expression["value_type"]["bits"] = 64.into(),
                1 => expression["constant_context"] = true.into(),
                2 => expression["span"]["file"] = "unlocked.h".into(),
                _ => unreachable!(),
            }
            let bytes = serde_json::to_vec_pretty(&forged).unwrap();
            let mut forged_lock = lock.clone();
            lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
                format!("{:x}", Sha256::digest(&bytes)).into();
            lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
            fs::write(project.artifact(), bytes).unwrap();
            fs::write(
                project.lock(),
                serde_json::to_vec_pretty(&forged_lock).unwrap(),
            )
            .unwrap();
            assert!(
                load_import(&project.config()).is_err(),
                "accepted mutation {mutation}"
            );
        }
    }
}

#[test]
fn unreachable_builtin_requires_an_unreachable_execution_path_offline() {
    let project = Project::with_fixture(
        "unreachable.cpp",
        "probe",
        "int probe(bool enter) noexcept { if (enter) { __builtin_unreachable(); } return 0; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = "verifying \"unreachable.cpp\";\nint32 probe(bool enter) { requires not enter; ensures result == 0; }\n";
    check_selected_claim_certificate(&project, &import, source);
    for hostile in [
        source.replace("requires not enter;", ""),
        source.replace("not enter", "enter"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        let error =
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .unwrap_err();
        assert!(
            error.message().contains("__builtin_unreachable"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn logical_negation_checks_full_width_truth_and_observer_results_offline() {
    for (cpp, helper, parameters, requires) in [
        (
            "bool probe(bool flag) noexcept { return !flag; }",
            "",
            "bool flag",
            "flag == false",
        ),
        (
            "bool probe(unsigned long value) noexcept { return !value; }",
            "",
            "uint64 value",
            "value == 0u64",
        ),
        (
            "bool ready() noexcept { return false; } bool probe() noexcept { return !ready(); }",
            "bool ready() { ensures result == false; }",
            "",
            "1 == 1",
        ),
        (
            "bool ready() noexcept { return false; } bool probe() noexcept { if (!ready()) { return true; } else { return false; } }",
            "bool ready() { ensures result == false; }",
            "",
            "1 == 1",
        ),
    ] {
        let project = Project::with_fixture("negation.cpp", "probe", cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"negation.cpp\";\n{helper}\nbool probe({parameters}) {{ requires {requires}; ensures result == true; }}\n"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace("ensures result == true;", "ensures result == false;");
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
        if parameters == "uint64 value" {
            let high = source
                .replace("value == 0u64", "value == 4294967296u64")
                .replace("result == true", "result == false");
            check_selected_claim_certificate(&project, &import, &high);
        }
    }
}

#[cfg(not(feature = "fast-gate"))]
#[test]
fn clang_export_is_deterministic_typed_and_loads_without_clang() {
    let project = Project::new();
    refresh_import(&project.config()).expect("export the semantic artifact");
    let first_artifact = fs::read(project.artifact()).unwrap();
    let first_lock = fs::read(project.lock()).unwrap();
    refresh_import(&project.config()).expect("repeat the same semantic export");
    assert_eq!(fs::read(project.artifact()).unwrap(), first_artifact);
    assert_eq!(fs::read(project.lock()).unwrap(), first_lock);

    let prepared = load_import(&project.config()).expect("load the locked artifact");
    assert_eq!(prepared.export().schema, 61);
    assert!(prepared.export().reachable_functions.is_empty());
    assert_eq!(prepared.logical_source(), "increment.cpp");
    assert_eq!(prepared.identity().len(), 64);
    assert_eq!(
        prepared.export().profile.compilation_directory,
        project.directory.to_string_lossy()
    );
    assert_eq!(
        prepared.export().profile.compilation_file,
        project.source_name
    );
    assert_eq!(
        prepared.export().profile.compilation_command,
        project.synthesized_arguments()
    );
    let function = &prepared.export().functions[0];
    assert_eq!(function.name, "increment");
    assert!(function.declaration_id.starts_with("c:@F@increment#"));
    assert_eq!(
        function.parameters[0].value_type,
        CppType::LvalueReference {
            pointee: Box::new(CppType::Integer {
                bits: 32,
                signed: true,
                is_const: false,
                source_aliases: Vec::new(),
            }),
        }
    );
    let CppStatement::Assign { value, .. } = &function.body[0] else {
        panic!("first semantic operation was not assignment")
    };
    assert!(matches!(
        value,
        CppExpression::Binary {
            operator: CppBinaryOperator::Add,
            left,
            right,
            ..
        } if matches!(left.as_ref(), CppExpression::Load { .. })
            && matches!(right.as_ref(), CppExpression::IntegerLiteral { value, .. } if value == "1")
    ));
    assert!(matches!(
        function.body[1],
        CppStatement::Return {
            value: CppExpression::Load { .. },
            ..
        }
    ));
    // The ordinary command locks the same unit as a project, repeatably, and
    // loading it needs no exporter.
    project.adopt();
    let lock = || {
        let output = Command::new(env!("CARGO_BIN_EXE_click"))
            .env("CLICK_CPP_EXPORTER", &project.exporter)
            .args(["capture", project.directory.to_str().unwrap()])
            .output()
            .expect("run the ordinary import command");
        assert!(
            output.status.success(),
            "click import failed: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        (
            fs::read(
                project
                    .directory
                    .join(".click/captures/demo/increment.cpp.click-cpp.json"),
            )
            .unwrap(),
            fs::read(project.directory.join(click::project::LOCK_NAME)).unwrap(),
        )
    };
    let first = lock();
    assert_eq!(lock(), first);
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after locking");
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIDECAR).unwrap();
    let VerificationInput::PreparedProgram(import) =
        read_verification_inputs(&sidecar, SIDECAR).expect("locked loading must not execute Clang")
    else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    assert_eq!(import.identity().len(), 64);
}

#[test]
fn out_of_tree_compilation_locks_dependency_root_and_rtti_profile() {
    let project = Project::constexpr_coin();
    let build = project.directory.join("build");
    fs::create_dir(&build).unwrap();
    let mut arguments = project.exception_enabled_compilation_arguments();
    for argument in &mut arguments {
        if argument == "-fno-rtti" {
            *argument = "-frtti".into();
        } else if argument == &project.source_name {
            *argument = project.source().to_string_lossy().into_owned();
        }
    }
    arguments.insert(1, format!("-I{}", project.directory.display()));
    let database = serde_json::json!([{
        "directory": build,
        "file": project.source(),
        "arguments": arguments,
        "output": "fixture.o"
    }]);
    fs::write(
        build.join("compile_commands.json"),
        serde_json::to_vec_pretty(&database).unwrap(),
    )
    .unwrap();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["compilation_database"] = "build/compile_commands.json".into();
    config["rtti"] = true.into();
    fs::write(
        project.config(),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();

    refresh_import(&project.config()).expect("export with out-of-tree build directory");
    let prepared = load_import(&project.config()).expect("offline import");
    assert!(prepared.export().profile.exceptions);
    assert!(prepared.export().profile.rtti);
    assert_eq!(prepared.export().dependencies, ["cstdint"]);
    // Click compiles in the unit root; the out-of-tree command's include
    // directory still reaches the project header.
    assert_eq!(
        prepared.export().profile.compilation_directory,
        project.directory.to_string_lossy()
    );

    fs::write(
        project.directory.join("cstdint"),
        "typedef long int64_t;\n// changed\n",
    )
    .unwrap();
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("dependency inventory differs")
    );
}

#[test]
fn every_opened_header_is_locked_even_outside_the_reachable_graph() {
    let project = Project::new();
    let header = project.directory.join("prelude.h");
    fs::write(&header, "#define PRELUDE 1\n").unwrap();
    fs::write(
        project.source(),
        format!("#include \"prelude.h\"\n{SOURCE}"),
    )
    .unwrap();

    refresh_import(&project.config()).expect("lock all opened headers");
    let prepared = load_import(&project.config()).expect("load unmodified header");
    assert!(prepared.export().dependencies.is_empty());
    let canonical_header = header.canonicalize().unwrap();
    assert!(
        prepared
            .export()
            .preprocessor_files
            .iter()
            .any(|file| { file.canonical_path == canonical_header.to_string_lossy() })
    );

    fs::write(&header, "#define PRELUDE 2\n").unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(
        error.contains("prelude.h") && error.contains("differs from its import lock"),
        "{error}"
    );
}

#[cfg(unix)]
#[test]
fn opened_header_symlink_target_is_locked() {
    use std::os::unix::fs::symlink;

    let project = Project::new();
    let header = project.directory.join("prelude.h");
    let first = project.directory.join("first.h");
    let second = project.directory.join("second.h");
    fs::write(&first, "#define PRELUDE 1\n").unwrap();
    fs::write(&second, "#define PRELUDE 1\n").unwrap();
    symlink(&first, &header).unwrap();
    fs::write(
        project.source(),
        format!("#include \"prelude.h\"\n{SOURCE}"),
    )
    .unwrap();

    refresh_import(&project.config()).expect("lock symlinked header");
    let prepared = load_import(&project.config()).expect("load original target");
    assert!(prepared.export().preprocessor_files.iter().any(|file| {
        file.accessed_path.ends_with("/prelude.h")
            && file.canonical_path == first.canonicalize().unwrap().to_string_lossy()
    }));

    fs::remove_file(&header).unwrap();
    symlink(&second, &header).unwrap();
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("changed its resolved target")
    );
}

#[test]
fn unit_arguments_are_locked_and_change_the_identity() {
    let project = Project::new();
    refresh_import(&project.config()).expect("export through the unit's command");
    let first = load_import(&project.config()).expect("load the locked unit");
    let first_identity = first.identity().to_string();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    assert_eq!(
        lock_section(&lock)["compilation_database_sha256"]
            .as_str()
            .unwrap()
            .len(),
        64
    );
    assert_eq!(
        lock_section(&lock)["profile"]["compilation_command"],
        serde_json::json!(project.synthesized_arguments())
    );

    // A changed argument changes the unit's description and its identity.
    let mut changed = project.compilation_arguments();
    changed.insert(changed.len() - 4, "-DCLICK_COMMAND_VARIANT=1".into());
    project.write_compilation_database_commands(&[changed.clone()]);
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("does not match its description"), "{error}");
    refresh_import(&project.config()).expect("refresh after an explicit argument change");
    let refreshed = load_import(&project.config()).unwrap();
    assert_ne!(refreshed.identity(), first_identity);
    *changed.last_mut().unwrap() = format!("{}.o", project.source_name);
    let after_rtti = changed.iter().position(|a| a == "-fno-rtti").unwrap() + 1;
    changed.insert(after_rtti, "-O0".to_string());
    assert_eq!(refreshed.export().profile.compilation_command, changed);

    // Arguments whose inputs the lock cannot inventory are refused.
    for untracked in ["@flags.rsp", "-include-pch", "-ivfsoverlay"] {
        let project = Project::new();
        let mut command = project.compilation_arguments();
        command.insert(1, untracked.into());
        project.write_compilation_database_commands(&[command]);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("untracked preprocessor input mode")
                || error.contains(&format!("unsupported C++ argument 1 `{untracked}`")),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn included_header_definition_is_selected_locked_and_validated() {
    let project = Project::header_function();
    refresh_import(&project.config()).expect("export the selected header definition");
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    assert_eq!(
        lock_section(&lock)["logical_source_sha256"]
            .as_str()
            .unwrap()
            .len(),
        64
    );

    let prepared = load_import(&project.config()).expect("load the locked header definition");
    assert_eq!(prepared.logical_source(), "selected.h");
    assert_eq!(prepared.export().logical_source, "selected.h");
    assert_eq!(prepared.export().profile.compilation_file, "driver.cpp");
    assert_eq!(prepared.export().functions[0].name, "header_increment");
    assert_eq!(prepared.export().functions[0].span.file, "selected.h");

    let sidecar = project.directory.join("demo.click");
    let sidecar_source = SIDECAR
        .replace("increment.cpp", "selected.h")
        .replace("increment", "header_increment");
    fs::write(&sidecar, &sidecar_source).unwrap();
    project.adopt();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let inputs = read_verification_inputs(&sidecar, &sidecar_source)
        .expect("load the header import offline");
    let VerificationInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the selected header function through the ordinary workflow");

    let stale = Project::header_function();
    refresh_import(&stale.config()).expect("lock the original header contents");
    let original_identity = load_import(&stale.config()).unwrap().identity().to_string();
    fs::write(
        stale.logical_header(),
        "inline int header_increment(int& value) noexcept {\n    value = value + 1;\n    return value;\n}\n\n",
    )
    .unwrap();
    let error = load_import(&stale.config()).unwrap_err();
    assert!(error.contains("logical source differs"), "{error}");
    refresh_import(&stale.config()).expect("refresh after changing the selected header");
    assert_ne!(
        load_import(&stale.config()).unwrap().identity(),
        original_identity
    );

    let wrong_location = Project::header_function();
    fs::write(
        wrong_location.directory.join("wrong.h"),
        "// not selected\n",
    )
    .unwrap();
    wrong_location.write_config_with_logical_source("header_increment", "wrong.h");
    let error = refresh_import(&wrong_location.config()).unwrap_err();
    assert!(error.contains("was not found"), "{error}");
    assert!(!wrong_location.artifact().exists());

    let ambiguous = Project::header_function();
    fs::write(
        ambiguous.logical_header(),
        "inline int header_increment(int& value) noexcept { return value; }\ninline int header_increment(const int& value) noexcept { return value; }\n",
    )
    .unwrap();
    let error = refresh_import(&ambiguous.config()).unwrap_err();
    assert!(error.contains("is overloaded"), "{error}");
    assert!(!ambiguous.artifact().exists());
}

#[test]
fn exception_enabled_profile_verifies_a_checked_normal_only_header_graph() {
    let project = Project::exception_enabled_header_function();
    refresh_import(&project.config()).expect("export the exception-enabled normal-only function");
    let prepared = load_import(&project.config()).expect("load the locked semantic artifact");
    assert!(prepared.export().profile.exceptions);
    assert_eq!(
        prepared.export().exception_behavior,
        CppExceptionBehavior::NormalOnly
    );
    assert!(!prepared.export().functions[0].declared_noexcept);
    assert!(prepared.export().records.is_empty());

    let sidecar = project.directory.join("demo.click");
    let sidecar_source = SIDECAR
        .replace("increment.cpp", "selected.h")
        .replace("increment", "header_increment");
    fs::write(&sidecar, &sidecar_source).unwrap();
    project.adopt();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let inputs = read_verification_inputs(&sidecar, &sidecar_source)
        .expect("load the exception-enabled header import offline");
    let VerificationInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the normal-only function through the ordinary workflow");

    let graph = Project::direct_call();
    fs::write(
        graph.source(),
        "int set_seven(int& value) {\n    value = 7;\n    return value;\n}\n\nint call_set_seven(int& value) {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    graph.write_exception_enabled_compilation_database();
    graph.write_config_with_profile("call_set_seven", "call_set_seven.cpp", true);
    refresh_import(&graph.config()).expect("export a closed normal-only direct-call graph");
    let graph = load_import(&graph.config()).unwrap();
    assert!(!graph.export().functions[0].declared_noexcept);
    assert_eq!(graph.export().reachable_functions.len(), 1);
    assert!(!graph.export().reachable_functions[0].declared_noexcept);
}

#[test]
fn scalar_int32_profile_verifies_a_typed_throw_and_keeps_its_lock_identity() {
    let project = Project::new();
    fs::write(project.source(), "int increment(int& value) { throw 7; }\n").unwrap();
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        true,
        "scalar_int32",
    );
    refresh_import(&project.config()).expect("export a typed scalar throw");
    let prepared = load_import(&project.config()).expect("load the locked scalar exception");
    assert_eq!(
        prepared.export().exception_behavior,
        CppExceptionBehavior::ScalarInt32
    );
    assert!(matches!(
        prepared.export().functions[0].body.as_slice(),
        [CppStatement::Throw { .. }]
    ));

    let sidecar_source = "verifying \"increment.cpp\";\n\
        int32 increment(int32& value) throws int32 {\n\
            ensures result == 0;\n\
            exceptional ensures exception == 7;\n\
        }\n";
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("a source throw must establish the declared exceptional outcome");

    let missing_signature = "verifying \"increment.cpp\";\n\
        int32 increment(int32& value) { ensures result == 0; }\n";
    let missing_signature_project = read_click_project(&sidecar, missing_signature).unwrap();
    verify_program_prepared_project(&missing_signature_project, &prepared)
        .expect_err("a source throw cannot cross an undeclared exceptional boundary");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn scalar_int32_profile_propagates_a_modular_throw_past_a_normal_call_continuation() {
    let project = Project::with_fixture(
        "caller.cpp",
        "caller",
        "int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 5;\n\
         }\n\
         int caller(bool should_throw) {\n\
             int result = helper(should_throw);\n\
             result = 5;\n\
             return result;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export both reachable outcomes");
    let prepared = load_import(&project.config()).expect("load the locked call graph");
    assert_eq!(prepared.export().reachable_functions.len(), 1);
    let sidecar_source = "verifying \"caller.cpp\";\n\
        int32 helper(bool should_throw) throws int32 {\n\
            ensures result == 5;\n\
            exceptional ensures exception == 7;\n\
        }\n\
        int32 caller(bool should_throw) throws int32 {\n\
            ensures result == 5;\n\
            exceptional ensures exception == 7;\n\
        }\n";
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("the caller must preserve the helper's exceptional exit");
    let expanded = expand_project_claim_source_by_label(
        &click_project,
        &ProgramInputs::program(&prepared),
        "caller.exceptional_ensures_0",
    )
    .expect("expand the caller's exceptional proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    // Session construction cold-verifies this complete program once.
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&rewritten, &prepared)
            .expect("retain the expanded scalar exception environment");
    let site = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&prepared),
        "caller.exceptional_ensures_0",
        0,
    )
    .expect("locate the expanded exceptional proof");
    session
        .verify_at_project(&expanded, site.line, site.column)
        .expect("retained audit must accept the expanded exceptional proof");

    let mut false_caller_claim = sidecar_source.to_string();
    let claim = "exceptional ensures exception == 7;";
    let caller_claim = false_caller_claim
        .rfind(claim)
        .expect("caller exception claim");
    false_caller_claim.replace_range(
        caller_claim..caller_claim + claim.len(),
        "exceptional ensures exception == 8;",
    );
    let false_project = read_click_project(&sidecar, &false_caller_claim).unwrap();
    verify_program_prepared_project(&false_project, &prepared)
        .expect_err("the caller cannot claim a different exception payload");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn scalar_int32_profile_catches_a_modular_throw_with_a_typed_payload() {
    let project = Project::with_fixture(
        "caller.cpp",
        "caller",
        "int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 7;\n\
         }\n\
         int caller(bool should_throw) {\n\
             try { helper(should_throw); }\n\
             catch (int caught) { return caught; }\n\
             return 7;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export the exact scalar handler");
    let prepared = load_import(&project.config()).expect("load the typed handler offline");
    let [
        CppStatement::TryCatchInt32 {
            binding,
            try_body,
            handler,
            ..
        },
        CppStatement::Return { .. },
    ] = prepared.export().functions[0].body.as_slice()
    else {
        panic!("the source try/catch was not retained as a typed handler");
    };
    assert_eq!(binding.name, "caught");
    assert!(matches!(
        binding.value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            is_const: false,
            ..
        }
    ));
    assert!(matches!(try_body.as_slice(), [CppStatement::Call { .. }]));
    assert!(matches!(handler.as_slice(), [CppStatement::Return { .. }]));

    let sidecar_source = "verifying \"caller.cpp\";\n\
        int32 helper(bool should_throw) throws int32 {\n\
            ensures result == 7;\n\
            exceptional ensures exception == 7;\n\
        }\n\
        int32 caller(bool should_throw) {\n\
            ensures result == 7;\n\
        }\n";
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("a caught modular throw should satisfy a nonthrowing caller signature");
    let with_payload = format!(
        r#"{sidecar_source} by {{
            outcomes {{
                returned => {{ step_until(function.exit); }}
                threw => {{ step_until(function.exit); }}
            }}
            outcomes {{
                returned => {{ close(); }}
                threw(error) => {{ have error == 7 by close(); close(); }}
            }}
        }}"#
    );
    let payload_project = click_project.with_entry_source(with_payload);
    let expanded_payload = expand_project_claim_source_by_label(
        &payload_project,
        &ProgramInputs::program(&prepared),
        "caller.contract",
    )
    .expect("expand the proof that names the caught payload at function exit");
    assert!(
        expanded_payload.contains("threw(error) =>"),
        "{expanded_payload}"
    );
    click::surface::without_implicit_solve_for_claim("caller.contract", || {
        verify_program_prepared_project(
            &payload_project.with_entry_source(expanded_payload),
            &prepared,
        )
        .map_err(|error| error.to_string())
    })
    .expect("the checked caught payload remains available on replay at function exit");
    let expanded = expand_project_claim_source_by_label(
        &click_project,
        &ProgramInputs::program(&prepared),
        "caller.ensures_0",
    )
    .expect("expand the handler proof");
    let returned_proof = expanded
        .split_once("returned => {")
        .and_then(|(_, rest)| rest.split_once("threw => {"))
        .map(|(returned, _)| returned)
        .expect("the expansion must keep a returned certificate");
    let threw_proof = expanded
        .split_once("threw => {")
        .map(|(_, threw)| threw)
        .expect("the expansion must keep a threw certificate");
    assert!(
        expanded.contains("outcomes {")
            && returned_proof.contains("have result == 7 by {")
            && threw_proof.contains("have result == 7 by {")
            && returned_proof.contains("close();")
            && threw_proof.contains("close();")
            && !expanded.contains("solve(")
            && !expanded.contains("trivial();"),
        "each outcome should retain its own explicit result certificate: {expanded}"
    );
    let rewritten = click_project.with_entry_source(expanded.clone());
    // Session construction cold-verifies this complete program once.
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&rewritten, &prepared)
            .expect("retain the expanded handler environment");
    let site = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&prepared),
        "caller.ensures_0",
        0,
    )
    .expect("locate the expanded handler proof");
    session
        .verify_at_project(&expanded, site.line, site.column)
        .expect("retained audit must accept the handler proof");

    let mut false_claim = sidecar_source.to_string();
    let caller_claim = false_claim
        .rfind("ensures result == 7;")
        .expect("caller claim");
    false_claim.replace_range(
        caller_claim..caller_claim + "ensures result == 7;".len(),
        "ensures result == 8;",
    );
    assert_ne!(false_claim, sidecar_source);
    let false_project = read_click_project(&sidecar, &false_claim).unwrap();
    verify_program_prepared_project(&false_project, &prepared)
        .expect_err("the handler cannot prove a false result claim");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn scalar_int32_profile_joins_a_caught_throw_inside_conditional_cleanup() {
    let project = Project::with_fixture(
        "caller.cpp",
        "caller",
        "struct Restore {\n\
             int* pointer;\n\
             int saved;\n\
             explicit Restore(int* slot) noexcept : pointer(slot), saved(*slot) { *pointer = 9; }\n\
             ~Restore() noexcept { *pointer = saved; }\n\
         };\n\
         int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 5;\n\
         }\n\
         int caller(int& value, bool construct, bool should_throw) {\n\
             try {\n\
                 if (construct) {\n\
                     Restore guard(&value);\n\
                     helper(should_throw);\n\
                 }\n\
             } catch (int caught) {\n\
                 return value;\n\
             }\n\
             return value;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export conditional cleanup and catch");
    let prepared = load_import(&project.config()).expect("load the conditional cleanup artifact");
    assert!(matches!(
        prepared.export().functions[0].body.as_slice(),
        [CppStatement::If { then_branch, else_branch, .. }, CppStatement::Return { .. }]
            if matches!(then_branch.as_slice(), [CppStatement::TryCatchInt32 { .. }])
                && else_branch.is_empty()
    ));

    let sidecar_source = r#"verifying "caller.cpp";
        Restore::Restore(int32* slot) {
            owns this->pointer;
            owns this->saved;
            owns slot[0..1];
            ensures this->pointer == slot;
            ensures this->saved == old(slot[0]);
            ensures slot[0] == 9;
            ensures separate(memory(*this), memory(this->pointer[0..1]));
        }
        Restore::~Restore() {
            requires separate(memory(*this), memory(this->pointer[0..1]));
            owns this->pointer;
            owns this->saved;
            owns this->pointer[0..1];
            ensures this->pointer == old(this->pointer);
            ensures this->saved == old(this->saved);
            ensures this->pointer[0] == old(this->saved);
        }
        int32 helper(bool should_throw) throws int32 {
            ensures result == 5;
            exceptional ensures exception == 7;
        }
        int32 caller(int32& value, bool construct, bool should_throw) {
            owns value;
            ensures result == old(value);
            ensures value == old(value);
        } by {
            branch {
                true => {
                    step();
                    step();
                    outcomes {
                        returned => {
                            step(); // destructor
                            step(); // retire the guard's automatic storage
                        }
                        threw => { step_until(function.exit); close(); }
                    }
                }
                false => { }
            }
            step();
            close();
        }
"#;
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &click_project,
        &ProgramInputs::program(&prepared),
        "caller.contract",
    )
    .expect("expand the mixed outcome proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &prepared)
        .expect("the expanded mixed outcome proof must reverify");
    // Session construction cold-verifies this complete program once.
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &prepared)
            .expect("retain the mixed outcome verification environment");
    let site = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&prepared),
        "caller.contract",
        0,
    )
    .expect("locate the rewritten branch proof");
    session
        .verify_at_project(&expanded, site.line, site.column)
        .expect("retained audit must accept the expanded mixed outcome proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: live C++ place-table import and proof rechecks, 5s"]
fn graph_place_indices_preserve_reference_calls_with_growing_unrelated_places() {
    for size in [4usize, 16, 64] {
        let parameters = (0..size)
            .map(|index| format!("int unused{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let locals = (0..size)
            .map(|index| format!("int local{index} = {index};"))
            .collect::<Vec<_>>()
            .join("\n");
        // Keep two reference-call/result mappings as the unrelated parameter
        // and local place tables grow through all three original sizes.
        let calls = "read(value);\n".repeat(2);
        let cpp = format!(
            "int read(int& value) noexcept {{ return value; }}\nint many({parameters}, int& value) noexcept {{ {locals} {calls} return value; }}"
        );
        let project = Project::with_fixture("places.cpp", "many", &cpp);
        refresh_import(&project.config())
            .expect("export growing caller parameters and local declarations");
        let import = load_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let parameters = (0..size)
            .map(|index| format!("int32 unused{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let source = format!(
            r#"verifying "places.cpp";
int32 read(int32& value) {{ owns value; ensures result == old(value); ensures value == old(value); }}
int32 many({parameters}, int32& value) {{ owns value; requires value == 7; ensures result == 7; ensures value == 7; }}
"#
        );
        check_selected_claim_certificate(&project, &import, &source);
        // Refuse the false result with a simple closer, rather than spending
        // the smart search budget trying to synthesize an impossible proof.
        let hostile = source
            .replace("ensures result == 7;", "ensures result == 8;")
            .replace(
                "ensures value == 7; }",
                "ensures value == 7; } by { step_until(function.exit); close(); }",
            );
        let sidecar = project.directory.join("bad.click");
        fs::write(&sidecar, &hostile).unwrap();
        let parsed = read_click_project(&sidecar, &hostile).unwrap();
        let error = verify_program_prepared_project(&parsed, &import)
            .expect_err("indexed reference calls must preserve the loaded value");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn catch_binding_names_do_not_escape_the_handler_scope() {
    let cpp = "int helper(bool fail) { if (fail) { throw 7; } return 7; }
        int caller(bool fail) { try { helper(fail); } catch (int caught) { return caught; }
        int caught = 7; return caught; }";
    let project = Project::with_fixture("caller.cpp", "caller", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config())
        .expect("a later local may reuse a finished catch binding name");
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let source = r#"verifying "caller.cpp";
int32 helper(bool fail) throws int32 { ensures result == 7; exceptional ensures exception == 7; }
int32 caller(bool fail) { ensures result == 7; }
"#;
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, source).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "caller.ensures_0",
    )
    .unwrap();
    let rewritten = parsed.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    // Session construction cold-verifies this complete program once.
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
    let position = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "caller.ensures_0",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
    let hostile = source.replace(
        "int32 caller(bool fail) { ensures result == 7; }",
        "int32 caller(bool fail) { ensures result == 8; }",
    );
    let hostile = read_click_project(&sidecar, &hostile).unwrap();
    verify_program_prepared_project(&hostile, &import)
        .expect_err("neither the local nor the caught payload is eight");
}

#[test]
fn scalar_int32_profile_rejects_unsupported_handler_shapes() {
    let cases = [
        (
            "catch_all",
            "try { throw 7; } catch (...) { return 7; }",
            "named by-value `int` binding",
        ),
        (
            "bool_binding",
            "try { throw 7; } catch (bool caught) { return 7; }",
            "named by-value `int` binding",
        ),
        (
            "multiple_handlers",
            "try { throw 7; } catch (int caught) { return caught; } catch (...) { return 7; }",
            "exactly one handler",
        ),
        (
            "try_local",
            "try { int local = 7; throw local; } catch (int caught) { return caught; }",
            "automatic C++ locals are currently supported only in the function body",
        ),
        (
            "handler_local",
            "try { throw 7; } catch (int caught) { int local = caught; return local; }",
            "automatic C++ locals are currently supported only in the function body",
        ),
        (
            "nested_handler",
            "try { try { throw 7; } catch (int inner) { return inner; } } catch (int caught) { return caught; }",
            "nested try/catch is outside the scalar int32 exception profile",
        ),
    ];
    for (name, handler, expected) in cases {
        let source = format!("int caller() {{ {handler} return 7; }}\n");
        let project = Project::with_fixture("caller.cpp", "caller", &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
        assert!(
            !project.artifact().exists(),
            "{name} was unexpectedly locked"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn scalar_int32_profile_unwinds_one_guard_on_both_paths() {
    let mdtest = parse_mdtest(
        Path::new("cpp_one_guard_unwind.md"),
        ONE_GUARD_UNWIND_MDTEST,
    )
    .unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let sidecar_source = mdtest.click_source.unwrap();
    let project = Project::with_fixture(&cpp.filename, &cpp.functions[0], &cpp.source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(
        &cpp.functions[0],
        &cpp.filename,
        true,
        &cpp.profile,
    );
    refresh_import(&project.config()).expect("export a guard local to the try block");
    let prepared = load_import(&project.config()).expect("load the guard artifact offline");
    let [
        CppStatement::TryCatchInt32 { try_body, .. },
        CppStatement::Return { .. },
    ] = prepared.export().functions[0].body.as_slice()
    else {
        panic!("the source try/catch was not retained");
    };
    let [CppStatement::Scope { body, cleanups, .. }] = try_body.as_slice() else {
        panic!("the guard's lifetime was not retained inside the try block");
    };
    assert!(matches!(
        body.as_slice(),
        [CppStatement::Declare { .. }, CppStatement::Call { .. }]
    ));
    assert!(matches!(
        cleanups.as_slice(),
        [CppCleanup::Destructor { .. }]
    ));

    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");
    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("normal and caught exceptional paths must restore the original value");
    let lowered = lower_import(&prepared).unwrap();
    let body = format!("{:?}", lowered.kernel_function().body());
    assert!(!body.contains("__click_cpp_unwind_exception"), "{body}");
    let expanded = expand_project_claim_source_by_label(
        &click_project,
        &ProgramInputs::program(&prepared),
        "guarded.contract",
    )
    .unwrap();
    assert!(
        !expanded.contains("__click_cpp_unwind_exception"),
        "{expanded}"
    );
    click::surface::without_implicit_solve_for_claim("guarded.contract", || {
        verify_program_prepared_project(&click_project.with_entry_source(expanded), &prepared)
            .map_err(|error| error.report())
    })
    .expect("typed cleanup payload survives expansion and cold replay");
}

#[test]
fn scalar_int32_profile_emits_function_scope_cleanup_edges_for_escaping_throws() {
    let project = Project::with_fixture(
        "escaping.cpp",
        "escaping",
        "struct Restore {\n\
             int* pointer;\n\
             explicit Restore(int* slot) noexcept : pointer(slot) { *pointer = 9; }\n\
             ~Restore() noexcept { *pointer = 42; }\n\
         };\n\
         int helper(bool should_throw) {\n\
             if (should_throw) { throw 7; }\n\
             return 5;\n\
         }\n\
         int escaping(int& value, bool throw_now, bool initializer_throws) {\n\
             Restore guard(&value);\n\
             if (throw_now) { throw 7; }\n\
             int ignored = helper(initializer_throws);\n\
             return value;\n\
         }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("escaping", "escaping.cpp", true, "scalar_int32");
    refresh_import(&project.config()).expect("export the escaping throw and initializer paths");
    let prepared = load_import(&project.config()).expect("load the checked C++ artifact");
    let lowered = lower_import(&prepared).expect("lower function-scope unwind edges");

    fn collect_unwind_edges<'a>(
        statement: &'a ProgramStatement,
        edges: &mut Vec<(&'a ProgramStatement, &'a ProgramStatement)>,
    ) {
        match statement {
            ProgramStatement::UnwindCleanup {
                body: try_body,
                cleanup: handler,
            } => {
                edges.push((try_body, handler));
                collect_unwind_edges(try_body, edges);
                collect_unwind_edges(handler, edges);
            }
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    collect_unwind_edges(statement, edges);
                }
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_unwind_edges(then_branch, edges);
                collect_unwind_edges(else_branch, edges);
            }
            ProgramStatement::TryCatchInt32 {
                try_body, handler, ..
            } => {
                collect_unwind_edges(try_body, edges);
                collect_unwind_edges(handler, edges);
            }
            _ => {}
        }
    }

    let mut edges = Vec::new();
    collect_unwind_edges(lowered.kernel_function().body(), &mut edges);
    assert_eq!(
        edges.len(),
        2,
        "both exceptional operations need cleanup edges"
    );
    for (_, cleanup) in &edges {
        assert!(
            contains_call(cleanup, "Restore::~Restore"),
            "each escaping edge must run the live destructor before the exception continues"
        );
    }
    assert!(
        edges
            .iter()
            .any(|(try_body, _)| matches!(try_body, ProgramStatement::Throw(_)))
    );
    assert!(edges.iter().any(|(try_body, _)| {
        matches!(try_body, ProgramStatement::Seq(sequence)
            if { let (declare, call) = (sequence.first(), &sequence.rest()); matches!(declare.as_ref(), ProgramStatement::Declare { name, .. } if name.is_named("ignored"))
                && contains_call(call, "helper") })
    }));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn scalar_int32_profile_rejects_hostile_cleanup_proofs() {
    let mdtest = parse_mdtest(
        Path::new("cpp_guard_unwind_before_second.md"),
        GUARD_BEFORE_SECOND_MDTEST,
    )
    .unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let sidecar_source = mdtest.click_source.unwrap();
    let project = Project::with_fixture(&cpp.filename, &cpp.functions[0], &cpp.source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(
        &cpp.functions[0],
        &cpp.filename,
        true,
        &cpp.profile,
    );
    refresh_import(&project.config()).expect("export the conditional cleanup frontier");
    let prepared = load_import(&project.config()).expect("load the cleanup artifact");
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");

    let click_project = read_click_project(&sidecar, &sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("the unmodified conditional cleanup proof must pass");

    let cases = [
        (
            "wrong_cleanup_order",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                "            step();\n            step();\n            have first_cell == old(first_cell);\n            step();\n            have second_cell == old(second_cell);",
                1,
            ),
            "the first guard cannot be restored before the second cleanup",
        ),
        (
            "omitted_cleanup",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                "            step();\n            step();\n            have second_cell == old(second_cell);",
                1,
            ),
            "a proof cannot omit a required destructor",
        ),
        // Each `step()` runs the next lowered statement, so a destructor runs
        // once however many steps a proof writes. Stepping past the return
        // is refused instead of executing a destructor again.
        (
            "duplicated_cleanup",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                &format!(
                    "{}            have second_cell == old(second_cell);",
                    "            step();\n".repeat(9)
                ),
                1,
            ),
            "a proof cannot execute a destructor twice",
        ),
        (
            "unconstructed_second_guard",
            sidecar_source.replacen(
                "        threw => {\n            have second_cell == old(second_cell);",
                "        threw => {\n            step();\n            have second_cell == 9;",
                1,
            ),
            "the exceptional path cannot destroy the skipped second guard",
        ),
        (
            "normal_value_on_exceptional_path",
            sidecar_source.replacen(
                "    exceptional ensures exception == 7;",
                "    exceptional ensures exception == 5;",
                1,
            ),
            "the normal return value cannot justify the exceptional outcome",
        ),
    ];

    for (name, hostile_source, expectation) in cases {
        assert_ne!(
            hostile_source, sidecar_source,
            "{name} did not change the hostile proof"
        );
        let hostile_project = read_click_project(&sidecar, &hostile_source).unwrap();
        assert!(
            verify_program_prepared_project(&hostile_project, &prepared).is_err(),
            "{expectation}: {name} unexpectedly verified"
        );
    }
}

#[test]
fn scalar_int32_profile_rejects_broader_guarded_try_shapes() {
    let mdtest = parse_mdtest(
        Path::new("cpp_one_guard_unwind.md"),
        ONE_GUARD_UNWIND_MDTEST,
    )
    .unwrap();
    let original_sidecar = mdtest.click_source.clone().unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let declaration = "        Restore guard(&value);\n        helper(should_throw);";
    assert!(cpp.source.contains(declaration));
    let cases = [
        (
            "late_guard",
            "        helper(should_throw);\n        Restore guard(&value);",
            "guard construction first",
        ),
        (
            "return_inside_try",
            "        Restore guard(&value);\n        return value;",
            "return from a guarded try region",
        ),
    ];
    for (name, replacement, expected) in cases {
        let source = cpp.source.replacen(declaration, replacement, 1);
        assert_ne!(source, cpp.source);
        let project = Project::with_fixture(&cpp.filename, &cpp.functions[0], &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(
            &cpp.functions[0],
            &cpp.filename,
            true,
            &cpp.profile,
        );
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
        assert!(
            !project.artifact().exists(),
            "{name} was unexpectedly locked"
        );
    }

    let destructor = "~Restore() noexcept { *pointer = saved; }";
    assert!(cpp.source.contains(destructor));
    let throwing_destructor =
        cpp.source
            .replacen(destructor, "~Restore() noexcept { throw 7; }", 1);
    let calling_destructor = format!(
        "int destructor_helper();\n{}\nint destructor_helper() {{ throw 7; }}\n",
        cpp.source.replacen(
            destructor,
            "~Restore() noexcept { destructor_helper(); *pointer = saved; }",
            1,
        )
    );
    for (name, source) in [
        ("throwing_destructor", throwing_destructor),
        ("calling_destructor", calling_destructor),
    ] {
        let project = Project::with_fixture(&cpp.filename, &cpp.functions[0], &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(
            &cpp.functions[0],
            &cpp.filename,
            true,
            &cpp.profile,
        );
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = if name == "calling_destructor" {
            format!(
                "{original_sidecar}\nint32 destructor_helper() throws int32 {{ ensures false; exceptional ensures exception == 7; }}\n"
            )
        } else {
            original_sidecar.clone()
        };
        let path = project.directory.join("destructor.click");
        fs::write(&path, &source).unwrap();
        let parsed = read_click_project(&path, &source).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect_err("a noexcept destructor's escaping exception must fail its proof");
    }
}

#[test]
fn scalar_int32_profile_rejects_a_non_int32_exception_payload() {
    let disabled = Project::new();
    disabled.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        false,
        "scalar_int32",
    );
    let error = refresh_import(&disabled.config())
        .expect_err("the scalar exception profile needs an exception-enabled compiler");
    assert!(error.contains("requires C++ exceptions enabled"), "{error}");

    let noexcept = Project::new();
    noexcept.write_exception_enabled_compilation_database();
    noexcept.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        true,
        "scalar_int32",
    );
    refresh_import(&noexcept.config())
        .expect("noexcept admission is followed by a checked nonthrowing contract");

    let project = Project::new();
    fs::write(
        project.source(),
        "int increment(int& value) { throw true; }\n",
    )
    .unwrap();
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(
        "increment",
        "increment.cpp",
        true,
        "scalar_int32",
    );
    let error = refresh_import(&project.config()).expect_err("bool is not an int32 exception");
    assert!(error.contains("exception payload"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
fn signed_int64_predicate_retains_alias_and_verifies_offline() {
    let project = Project::int64_predicate();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, INT64_PREDICATE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the signed-64 predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the predicate artifact offline");
    assert_eq!(import.export().schema, 61);
    assert!(import.export().profile.exceptions);
    assert!(!import.export().functions[0].declared_noexcept);
    assert!(matches!(
        import.export().functions[0].return_type,
        CppType::Boolean {
            bits: 8,
            is_const: false
        }
    ));
    let CppType::LvalueReference { pointee } =
        &import.export().functions[0].parameters[0].value_type
    else {
        panic!("CAmount parameter did not retain reference type")
    };
    let CppType::Integer {
        bits: 64,
        signed: true,
        is_const: true,
        source_aliases,
    } = pointee.as_ref()
    else {
        panic!("CAmount parameter did not retain its signed-64 alias: {pointee:#?}")
    };
    let [alias] = source_aliases.as_slice() else {
        panic!("CAmount parameter did not retain exactly one direct alias")
    };
    assert_eq!(alias.name, "CAmount");
    assert!(!alias.declaration_id.is_empty());
    assert_eq!(alias.span.file, "money_nonnegative.cpp");
    assert_eq!(alias.span.start_line, 1);
    assert!(matches!(
        import.export().functions[0].body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::GreaterEqual,
                left,
                right,
                ..
            },
            ..
        }] if matches!(left.as_ref(), CppExpression::Load { .. })
            && matches!(right.as_ref(), CppExpression::IntegralCast { value, .. }
                if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. } if value == "0"))
    ));

    let lowered = lower_import(&import).expect("lower the predicate directly to the kernel");
    assert_eq!(lowered.kernel_function().return_type(), ProgramType::Bool);
    assert_eq!(
        lowered.kernel_function().parameters()[0].program_type(),
        ProgramType::Int64Pointer
    );
    assert!(lowered.kernel_function().parameters()[0].pointee_is_constant());

    let click_project = read_click_project(&sidecar, INT64_PREDICATE_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the signed-64 comparison through the offline artifact");

    let false_source = INT64_PREDICATE_SIDECAR.replace(">= 0i64", "> 0i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn signed_int64_predicate_admits_inequality_and_rejects_unsupported_siblings() {
    let inequality = Project::int64_predicate();
    fs::write(
        inequality.source(),
        INT64_PREDICATE_SOURCE.replace("nValue >= 0", "nValue != 0"),
    )
    .unwrap();
    refresh_import(&inequality.config()).unwrap();
    let import = load_import(&inequality.config()).unwrap();
    let proof = INT64_PREDICATE_SIDECAR.replace(">= 0i64", "!= 0i64");
    check_first_claim_certificate(&inequality, &import, &proof);

    let disjunction = Project::int64_predicate();
    fs::write(
        disjunction.source(),
        INT64_PREDICATE_SOURCE.replace("nValue >= 0", "nValue >= 0 || nValue <= 2100000000000000L"),
    )
    .unwrap();
    let error = refresh_import(&disjunction.config()).unwrap_err();
    assert!(error.contains("built-in bool && bool only"), "{error}");

    let unsigned = Project::int64_predicate();
    fs::write(
        unsigned.source(),
        INT64_PREDICATE_SOURCE.replace("typedef long CAmount", "typedef unsigned long CAmount"),
    )
    .unwrap();
    let error = refresh_import(&unsigned.config()).unwrap_err();
    assert!(error.contains("const signed-64 reference"), "{error}");

    let mutable = Project::int64_predicate();
    fs::write(
        mutable.source(),
        INT64_PREDICATE_SOURCE.replace("const CAmount&", "CAmount&"),
    )
    .unwrap();
    let error = refresh_import(&mutable.config()).unwrap_err();
    assert!(error.contains("const signed-64 reference"), "{error}");
}

#[test]
fn constexpr_coin_retains_alias_chain_and_verifies_offline() {
    let project = Project::constexpr_coin();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_COIN_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the constexpr coin predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the constexpr artifact offline");
    assert_eq!(import.export().schema, 61);
    assert_eq!(import.export().dependencies, ["cstdint"]);
    let CppType::LvalueReference { pointee } =
        &import.export().functions[0].parameters[0].value_type
    else {
        panic!("CAmount parameter did not retain reference type")
    };
    let CppType::Integer {
        bits: 64,
        signed: true,
        is_const: true,
        source_aliases,
    } = pointee.as_ref()
    else {
        panic!("CAmount parameter did not retain its alias chain: {pointee:#?}")
    };
    assert_eq!(
        source_aliases
            .iter()
            .map(|alias| alias.name.as_str())
            .collect::<Vec<_>>(),
        ["CAmount", "int64_t"]
    );
    assert_eq!(source_aliases[0].span.file, "at_least_one_coin.cpp");
    assert_eq!(source_aliases[1].span.file, "cstdint");

    let [constant] = import.export().constants.as_slice() else {
        panic!("COIN was not captured as the sole reachable constant")
    };
    assert_eq!(constant.name, "COIN");
    assert_eq!(constant.evaluated_value, "100000000");
    assert!(matches!(
        &constant.initializer,
        CppExpression::IntegralCast { value, .. }
            if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. }
                if value == "100000000")
    ));
    assert!(matches!(
        import.export().functions[0].body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::GreaterEqual,
                right,
                ..
            },
            ..
        }] if matches!(right.as_ref(), CppExpression::ConstantReference { constant: reference, .. }
            if reference.declaration_id == constant.declaration_id && reference.name == "COIN")
    ));

    let lowered = lower_import(&import).expect("lower the constexpr predicate directly");
    assert_eq!(lowered.kernel_function().return_type(), ProgramType::Bool);
    let click_project = read_click_project(&sidecar, CONSTEXPR_COIN_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the constexpr comparison through the offline artifact");

    let false_source = CONSTEXPR_COIN_SIDECAR.replace(">= 100000000i64", "> 100000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );

    fs::write(project.directory.join("cstdint"), "typedef int int64_t;\n").unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("dependency inventory differs"), "{error}");
}

#[test]
fn constexpr_coin_rejects_unlocked_mutable_and_nonleaf_constants() {
    let mutable = Project::constexpr_coin();
    fs::write(
        mutable.source(),
        CONSTEXPR_COIN_SOURCE.replace("static constexpr CAmount", "static CAmount"),
    )
    .unwrap();
    let error = refresh_import(&mutable.config()).unwrap_err();
    assert!(error.contains("static constexpr"), "{error}");

    let nonleaf = Project::constexpr_coin();
    fs::write(
        nonleaf.source(),
        CONSTEXPR_COIN_SOURCE.replace("100000000;", "50000000 + 50000000;"),
    )
    .unwrap();
    let error = refresh_import(&nonleaf.config()).unwrap_err();
    assert!(
        error.contains("literal leaf or one dependent multiplication"),
        "{error}"
    );

    let mut unlocked = Project::constexpr_coin();
    unlocked.dependencies.clear();
    unlocked.write_config_with_profile("at_least_one_coin", "at_least_one_coin.cpp", true);
    let error = refresh_import(&unlocked.config()).unwrap_err();
    assert!(
        error.contains("differ from configured dependencies"),
        "{error}"
    );
}

#[test]
fn constexpr_max_money_retains_checked_dependency_and_verifies_offline() {
    let project = Project::constexpr_max_money();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_MAX_MONEY_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the dependent constexpr predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the dependent artifact offline");
    assert_eq!(import.export().schema, 61);
    let [coin, max_money] = import.export().constants.as_slice() else {
        panic!("COIN and MAX_MONEY were not captured as one ordered dependency")
    };
    assert_eq!(coin.name, "COIN");
    assert_eq!(coin.evaluated_value, "100000000");
    assert_eq!(max_money.name, "MAX_MONEY");
    assert_eq!(max_money.evaluated_value, "2100000000000000");
    assert!(matches!(
        &max_money.initializer,
        CppExpression::Binary {
            operator: CppBinaryOperator::Multiply,
            left,
            right,
            ..
        } if matches!(left.as_ref(), CppExpression::IntegralCast { value, .. }
            if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. }
                if value == "21000000"))
            && matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
                if constant.declaration_id == coin.declaration_id && constant.name == "COIN")
    ));
    assert!(matches!(
        import.export().functions[0].body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::GreaterEqual,
                right,
                ..
            },
            ..
        }] if matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
            if constant.declaration_id == max_money.declaration_id
                && constant.name == "MAX_MONEY")
    ));

    let lowered = lower_import(&import).expect("lower the dependent constexpr predicate");
    assert_eq!(lowered.kernel_function().return_type(), ProgramType::Bool);
    let click_project = read_click_project(&sidecar, CONSTEXPR_MAX_MONEY_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the dependent constexpr comparison offline");

    let false_source =
        CONSTEXPR_MAX_MONEY_SIDECAR.replace(">= 2100000000000000i64", "> 2100000000000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn signed_int64_less_equal_verifies_max_money_upper_bound_offline() {
    let project = Project::constexpr_max_money_less_equal();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_MAX_MONEY_LE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the signed-64 upper-bound predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the upper-bound artifact offline");
    assert_eq!(import.export().schema, 61);
    let [coin, max_money] = import.export().constants.as_slice() else {
        panic!("the upper-bound artifact lost the MAX_MONEY dependency graph")
    };
    assert_eq!(coin.name, "COIN");
    assert_eq!(max_money.name, "MAX_MONEY");
    assert!(matches!(
        import.export().functions[0].body.as_slice(),
        [CppStatement::Return {
            value: CppExpression::Binary {
                operator: CppBinaryOperator::LessEqual,
                right,
                ..
            },
            ..
        }] if matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
            if constant.declaration_id == max_money.declaration_id
                && constant.name == "MAX_MONEY")
    ));

    let lowered = lower_import(&import).expect("lower signed-64 less-equal directly");
    assert_eq!(lowered.kernel_function().return_type(), ProgramType::Bool);
    let click_project = read_click_project(&sidecar, CONSTEXPR_MAX_MONEY_LE_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the inclusive MAX_MONEY upper bound offline");

    let false_source =
        CONSTEXPR_MAX_MONEY_LE_SIDECAR.replace("<= 2100000000000000i64", "< 2100000000000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn built_in_cpp_logical_and_verifies_inclusive_money_range_offline() {
    let project = Project::constexpr_max_money_range();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTEXPR_MAX_MONEY_RANGE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the built-in short-circuit predicate");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load the range artifact offline");
    assert_eq!(import.export().schema, 61);
    let [coin, max_money] = import.export().constants.as_slice() else {
        panic!("the range artifact lost the ordered MAX_MONEY dependency graph")
    };
    assert_eq!(coin.name, "COIN");
    assert_eq!(max_money.name, "MAX_MONEY");
    let [
        CppStatement::Return {
            value:
                CppExpression::Binary {
                    operator: CppBinaryOperator::LogicalAnd,
                    left,
                    right,
                    value_type:
                        CppType::Boolean {
                            bits: 8,
                            is_const: false,
                        },
                    ..
                },
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the range return did not retain Clang's built-in logical-and node")
    };
    assert!(matches!(left.as_ref(), CppExpression::Binary {
        operator: CppBinaryOperator::GreaterEqual,
        right,
        ..
    } if matches!(right.as_ref(), CppExpression::IntegralCast { value, .. }
        if matches!(value.as_ref(), CppExpression::IntegerLiteral { value, .. }
            if value == "0"))));
    assert!(matches!(right.as_ref(), CppExpression::Binary {
        operator: CppBinaryOperator::LessEqual,
        right,
        ..
    } if matches!(right.as_ref(), CppExpression::ConstantReference { constant, .. }
        if constant.declaration_id == max_money.declaration_id
            && constant.name == "MAX_MONEY")));

    let lowered = lower_import(&import).expect("lower built-in C++ && directly");
    assert_eq!(lowered.kernel_function().return_type(), ProgramType::Bool);
    assert!(matches!(lowered.kernel_function().body(),
        ProgramStatement::Return(ProgramExpression::Cast {
            expression,
            target_type: ProgramType::Bool,
            ..
        }) if matches!(expression.as_ref(), ProgramExpression::And(_, _))));
    let click_project = read_click_project(&sidecar, CONSTEXPR_MAX_MONEY_RANGE_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the inclusive range contract offline");

    let false_source = CONSTEXPR_MAX_MONEY_RANGE_SIDECAR
        .replace("<= 2100000000000000i64", "< 2100000000000000i64");
    let false_project = read_click_project(&sidecar, &false_source).unwrap();
    let error = verify_program_prepared_project(&false_project, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn built_in_cpp_logical_and_accepts_checked_integer_to_bool_conversion() {
    let project = Project::constexpr_max_money_range();
    fs::write(
        project.source(),
        CONSTEXPR_MAX_MONEY_SOURCE.replace(
            "value >= 0 && value <= MAX_MONEY",
            "value && value <= MAX_MONEY",
        ),
    )
    .unwrap();
    refresh_import(&project.config()).unwrap();
    lower_import(&load_import(&project.config()).unwrap()).unwrap();
}

#[test]
fn constexpr_max_money_accepts_deeper_constant_graphs_and_rejects_new_initializer_semantics() {
    let addition = Project::constexpr_max_money();
    fs::write(
        addition.source(),
        CONSTEXPR_MAX_MONEY_SOURCE.replace("21000000 * COIN", "21000000 + COIN"),
    )
    .unwrap();
    let error = refresh_import(&addition.config()).unwrap_err();
    assert!(
        error.contains("literal leaf or one dependent multiplication"),
        "{error}"
    );

    let third = Project::constexpr_max_money();
    let source = CONSTEXPR_MAX_MONEY_SOURCE
        .replace(
            "static constexpr CAmount MAX_MONEY = 21000000 * COIN;",
            "static constexpr CAmount MAX_MONEY = 21000000 * COIN;\nstatic constexpr CAmount TOO_MUCH = 2 * MAX_MONEY;",
        )
        .replace("value >= MAX_MONEY", "value >= TOO_MUCH");
    fs::write(third.source(), source).unwrap();
    refresh_import(&third.config()).unwrap();
    let import = load_import(&third.config()).unwrap();
    assert_eq!(import.export().constants.len(), 3);
    lower_import(&import).unwrap();

    let runtime_multiply = Project::constexpr_max_money();
    fs::write(
        runtime_multiply.source(),
        CONSTEXPR_MAX_MONEY_SOURCE.replace("value >= MAX_MONEY", "value >= MAX_MONEY * 1"),
    )
    .unwrap();
    refresh_import(&runtime_multiply.config()).unwrap();
    lower_import(&load_import(&runtime_multiply.config()).unwrap()).unwrap();
}

#[test]
fn exception_enabled_profile_rejects_exception_and_object_semantics() {
    let throwing = Project::new();
    fs::write(
        throwing.source(),
        "int increment(int& value) {\n    throw value;\n}\n",
    )
    .unwrap();
    throwing.write_exception_enabled_compilation_database();
    throwing.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&throwing.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("throw expressions are outside"), "{error}");
    assert!(!throwing.artifact().exists());

    let catching = Project::new();
    fs::write(
        catching.source(),
        "int increment(int& value) {\n    try { value = value + 1; } catch (...) { return 0; }\n    return value;\n}\n",
    )
    .unwrap();
    catching.write_exception_enabled_compilation_database();
    catching.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&catching.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("try/catch is outside"), "{error}");
    assert!(!catching.artifact().exists());

    let unresolved = Project::direct_call();
    fs::write(
        unresolved.source(),
        "int set_seven(int& value);\n\nint call_set_seven(int& value) {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    unresolved.write_exception_enabled_compilation_database();
    unresolved.write_config_with_profile("call_set_seven", "call_set_seven.cpp", true);
    let error = refresh_import(&unresolved.config()).unwrap_err();
    assert!(
        error.contains("external C++ function `set_seven` must be noexcept"),
        "{error}"
    );
    assert!(!unresolved.artifact().exists());

    let object = Project::new();
    fs::write(
        object.source(),
        "struct Box { int stored; ~Box() noexcept { stored = 0; } };\nint increment(int& value) {\n    Box box{value};\n    return box.stored;\n}\n",
    )
    .unwrap();
    object.write_exception_enabled_compilation_database();
    object.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&object.config()).unwrap_err();
    assert!(error.contains("increment.cpp:3"), "{error}");
    assert!(
        error.contains("local objects require trivial destruction"),
        "{error}"
    );
    assert!(!object.artifact().exists());
}

#[test]
fn locked_cpp_function_verifies_through_the_shared_sidecar_path_offline() {
    let project = Project::new();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the C++ import explicitly");
    project.adopt();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs =
        read_verification_inputs(&sidecar, &click_source).expect("load the locked sidecar input");
    let VerificationInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify the directly lowered C++ function");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
                VerifiedClaim::ExceptionalEnsure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2],
        "the grouped proof checks returned ownership plus both value postconditions"
    );
    assert!(
        verified
            .iter()
            .all(|theorem| { theorem.import_identity.as_deref() == Some(import.identity()) })
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn locked_cpp_branch_and_early_return_verify_through_the_shared_sidecar_path() {
    let project = Project::branch_return();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, BRANCH_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the branching C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load branching artifact offline");
    let source = &import.export().functions[0];
    assert_eq!(source.parameters.len(), 2);
    assert!(matches!(
        source.parameters[0].value_type,
        CppType::Boolean {
            bits: 8,
            is_const: false,
        }
    ));
    assert!(matches!(
        source.body.as_slice(),
        [
            CppStatement::Assign { .. },
            CppStatement::If {
                then_branch,
                else_branch,
                ..
            },
            CppStatement::Assign { .. },
            CppStatement::Return { .. },
        ] if matches!(then_branch.as_slice(), [CppStatement::Return { .. }])
            && else_branch.is_empty()
    ));

    let lowered = lower_import(&import).expect("lower the typed branch directly");
    assert_eq!(
        lowered.kernel_function().parameters()[0].program_type(),
        ProgramType::Bool
    );
    assert!(contains_if(lowered.kernel_function().body()));

    project.adopt();
    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_verification_inputs(&sidecar, &click_source).unwrap();
    let VerificationInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();

    let sites = project_smart_tactic_source_sites(&click_project, &ProgramInputs::program(&import))
        .unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["implicit tail"]
    );
    let implicit = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "choose.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        implicit.line,
        implicit.column,
    )
    .expect("expand the branch execution into a checkable source proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded branch proof must reverify");
    // Construction checks the same complete original and returns its claim metadata.
    let (session, verified) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &import)
            .expect("retain the original branch verification environment");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
                VerifiedClaim::ExceptionalEnsure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 0, 1, 2],
        "both return paths certify returned ownership and both postconditions"
    );

    let next = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "choose.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded branch proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn const_reference_preserves_qualification_and_may_alias_a_mutable_reference() {
    let project = Project::const_reference_alias();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONST_REFERENCE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the const-reference C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load const-reference artifact offline");
    let source = &import.export().functions[0];
    assert_eq!(source.parameters.len(), 2);
    assert_eq!(
        source.parameters[0].value_type,
        CppType::LvalueReference {
            pointee: Box::new(CppType::Integer {
                bits: 32,
                signed: true,
                is_const: false,
                source_aliases: Vec::new(),
            }),
        }
    );
    assert_eq!(
        source.parameters[1].value_type,
        CppType::LvalueReference {
            pointee: Box::new(CppType::Integer {
                bits: 32,
                signed: true,
                is_const: true,
                source_aliases: Vec::new(),
            }),
        }
    );

    let lowered = lower_import(&import).expect("lower both C++ reference qualifiers directly");
    let parameters = lowered.kernel_function().parameters();
    assert_eq!(parameters[0].program_type(), ProgramType::Int32Pointer);
    assert!(!parameters[0].pointee_is_constant());
    assert_eq!(parameters[1].program_type(), ProgramType::Int32Pointer);
    assert!(parameters[1].pointee_is_constant());

    project.adopt();
    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_verification_inputs(&sidecar, &click_source).unwrap();
    let VerificationInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();

    let sites = project_smart_tactic_source_sites(&click_project, &ProgramInputs::program(&import))
        .unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec![click::instrumentation::IMPLICIT_TAIL_TACTIC]
    );
    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "write_then_read.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the aliased reference execution into a checkable proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded const-reference proof must reverify");
    // Construction checks the same complete original and returns its claim metadata.
    let (session, verified) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &import)
            .expect("retain the const-reference verification environment");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
                VerifiedClaim::ExceptionalEnsure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2],
        "the proof returns ownership and checks both postconditions without an inferred view"
    );

    let next = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "write_then_read.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded const-reference proof");

    let mutable_signature =
        CONST_REFERENCE_SIDECAR.replace("const int32& readable", "int32& readable");
    fs::write(&sidecar, &mutable_signature).unwrap();
    let mismatched_project = read_click_project(&sidecar, &mutable_signature).unwrap();
    let error = verify_program_prepared_project(&mismatched_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("signature mismatch for `write_then_read` parameter 2"),
        "{}",
        error.message()
    );
}

fn contains_if(statement: &ProgramStatement) -> bool {
    match statement {
        ProgramStatement::If { .. } => true,
        ProgramStatement::Seq(statements) => {
            statements.iter().any(|statement| contains_if(statement))
        }
        _ => false,
    }
}

fn contains_call(statement: &ProgramStatement, expected: &str) -> bool {
    match statement {
        ProgramStatement::Call { function_name, .. }
        | ProgramStatement::CallResult { function_name, .. }
        | ProgramStatement::CallConstruct { function_name, .. } => {
            function_name == expected
                || click::surface::source_display_name(function_name).as_deref() == Some(expected)
        }
        ProgramStatement::Seq(statements) => statements
            .iter()
            .any(|statement| contains_call(statement, expected)),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => contains_call(then_branch, expected) || contains_call(else_branch, expected),
        _ => false,
    }
}

/// The functions `statement` calls, in order, as C++ names them.
fn call_order(statement: &ProgramStatement) -> Vec<String> {
    fn visit(statement: &ProgramStatement, calls: &mut Vec<String>) {
        match statement {
            ProgramStatement::Call { function_name, .. } => calls.push(
                click::surface::source_display_name(function_name)
                    .unwrap_or_else(|| function_name.clone()),
            ),
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    visit(statement, calls);
                }
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, calls);
                visit(else_branch, calls);
            }
            _ => {}
        }
    }
    let mut calls = Vec::new();
    visit(statement, &mut calls);
    calls
}

fn destructor_object_order<'a>(statement: &'a ProgramStatement, destructor: &str) -> Vec<&'a str> {
    fn visit<'a>(statement: &'a ProgramStatement, destructor: &str, objects: &mut Vec<&'a str>) {
        match statement {
            ProgramStatement::Call {
                function_name,
                arguments,
                ..
            } if function_name == destructor
                || click::surface::source_display_name(function_name).as_deref()
                    == Some(destructor) =>
            {
                if let [ProgramExpression::Cast { expression, .. }] = arguments.as_slice()
                    && let ProgramExpression::Variable(name) = expression.as_ref()
                {
                    objects.push(name.source_name());
                }
            }
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    visit(statement, destructor, objects);
                }
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, destructor, objects);
                visit(else_branch, destructor, objects);
            }
            _ => {}
        }
    }
    let mut objects = Vec::new();
    visit(statement, destructor, &mut objects);
    objects
}

fn contains_raw_aggregate_destination(statement: &ProgramStatement, expected: &str) -> bool {
    match statement {
        ProgramStatement::DeclareAggregate {
            name,
            kind: click::kernel::AggregateDeclarationKind::ConstructionDestination,
            ..
        } => name.is_named(expected),
        ProgramStatement::Seq(statements) => statements
            .iter()
            .any(|statement| contains_raw_aggregate_destination(statement, expected)),
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            contains_raw_aggregate_destination(then_branch, expected)
                || contains_raw_aggregate_destination(else_branch, expected)
        }
        _ => false,
    }
}

fn contains_scalar_local_pipeline(
    statement: &ProgramStatement,
    call_local: &str,
    value_local: &str,
    callee: &str,
) -> [bool; 4] {
    let mut found = [false; 4];
    fn visit(
        statement: &ProgramStatement,
        call_local: &str,
        value_local: &str,
        callee: &str,
        found: &mut [bool; 4],
    ) {
        match statement {
            ProgramStatement::Declare {
                name,
                program_type: ProgramType::Int32,
                ..
            } if name.is_named(call_local) => found[0] = true,
            ProgramStatement::CallResult { function_name, .. } if function_name == callee => {
                found[1] = true
            }
            ProgramStatement::Declare {
                name,
                program_type: ProgramType::Int32,
                ..
            } if name.is_named(value_local) => found[2] = true,
            ProgramStatement::Assign { name, .. } if name.is_named(value_local) => found[3] = true,
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    visit(statement, call_local, value_local, callee, found);
                }
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, call_local, value_local, callee, found);
                visit(else_branch, call_local, value_local, callee, found);
            }
            _ => {}
        }
    }
    visit(statement, call_local, value_local, callee, &mut found);
    found
}

fn contains_local_aggregate_pipeline(statement: &ProgramStatement, local: &str) -> [bool; 3] {
    let mut found = [false; 3];
    fn visit(statement: &ProgramStatement, local: &str, found: &mut [bool; 3]) {
        match statement {
            ProgramStatement::DeclareAggregate { name, layout, .. } if name.is_named(local) => {
                found[0] = layout.size_bytes() == 16
                    && layout.alignment_bytes() == 8
                    && layout.fields().len() == 2;
            }
            ProgramStatement::TypedStore {
                pointer,
                value_type,
                ..
            } => {
                if matches!(pointer, ProgramExpression::Variable(name) if name.is_named(local))
                    && *value_type == ProgramType::Int32Pointer
                {
                    found[1] = true;
                }
                if let ProgramExpression::PointerOffsetBytes { pointer, bytes } = pointer
                    && matches!(pointer.as_ref(), ProgramExpression::Variable(name) if name.is_named(local))
                {
                    if *bytes == 0.into() && *value_type == ProgramType::Int32Pointer {
                        found[1] = true;
                    }
                    if *bytes == 8.into() && *value_type == ProgramType::Int32 {
                        found[2] = true;
                    }
                }
            }
            ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    visit(statement, local, found);
                }
            }
            ProgramStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                visit(then_branch, local, found);
                visit(else_branch, local, found);
            }
            _ => {}
        }
    }
    visit(statement, local, &mut found);
    found
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: two live Clang exports and a prepared proof"]
fn cpp_function_root_checks_an_unsupported_sibling_only_when_called() {
    let source = r#"int sibling() noexcept {
    goto done;
done:
    return 42;
}
int selected() noexcept { return 42; }
"#;
    let project = Project::with_fixture("roots.cpp", "selected", source);
    let proof = r#"verifying "roots.cpp";
int32 selected() { ensures result == 42; }
"#;
    let sidecar = project.directory.join("roots.click");
    fs::write(&sidecar, proof).unwrap();

    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [root] = import.export().functions.as_slice() else {
        panic!("expected one selected function");
    };
    assert_eq!(root.name, "selected");
    assert!(import.export().reachable_functions.is_empty());
    let click_project = read_click_project(&sidecar, proof).unwrap();
    verify_program_prepared_project(&click_project, &import).unwrap();

    let caller = source.replace("return 42; }", "return sibling(); }");
    fs::write(project.source(), caller).unwrap();
    let error = refresh_import(&project.config()).expect_err("a called sibling must be exported");
    assert!(error.contains("roots.cpp:2:5"), "{error}");
    assert!(error.contains("unsupported statement"), "{error}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn direct_cpp_call_exports_reachable_definition_and_verifies_modularly_offline() {
    let project = Project::direct_call();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, DIRECT_CALL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the resolved C++ call graph");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the call graph artifact offline");
    assert_eq!(import.export().schema, 61);
    assert_eq!(import.export().functions[0].name, "call_set_seven");
    assert_eq!(import.export().reachable_functions.len(), 1);
    let reachable = &import.export().reachable_functions[0];
    assert_eq!(reachable.name, "set_seven");
    let CppStatement::Call {
        callee, arguments, ..
    } = &import.export().functions[0].body[0]
    else {
        panic!("first caller operation was not a resolved call")
    };
    assert_eq!(callee.declaration_id, reachable.declaration_id);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Reference { place }]
            if place.declaration_id == import.export().functions[0].parameters[0].declaration_id
    ));

    let lowered = lower_import(&import).expect("lower both C++ functions directly");
    assert!(contains_call(lowered.kernel_function().body(), "set_seven"));
    assert_eq!(lowered.reachable_kernel_functions().len(), 1);
    assert_eq!(lowered.reachable_kernel_functions()[0].name(), "set_seven");

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();

    let sites = project_smart_tactic_source_sites(&click_project, &ProgramInputs::program(&import))
        .unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec![click::instrumentation::IMPLICIT_TAIL_TACTIC; 2]
    );
    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "call_set_seven.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the caller's modular execution proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded modular C++ proof must reverify");
    // Construction checks the same complete original and returns its claim metadata.
    let (session, verified) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &import)
            .expect("retain the modular C++ verification environment");
    assert_eq!(verified.len(), 6);

    let next = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "call_set_seven.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded caller proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn scalar_local_captures_a_direct_call_result_and_verifies_offline() {
    let project = Project::scalar_local();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SCALAR_LOCAL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the typed C++ local and call result");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the scalar-local artifact offline");
    assert_eq!(import.export().schema, 61);
    assert_eq!(import.export().functions[0].name, "relay_value");
    assert_eq!(import.export().reachable_functions.len(), 1);
    let reachable = &import.export().reachable_functions[0];
    assert_eq!(reachable.name, "read_value");
    let [
        CppStatement::Declare {
            local: captured,
            initializer: CppInitializer::Call {
                callee, arguments, ..
            },
            ..
        },
        CppStatement::Declare {
            local: relayed,
            initializer: CppInitializer::Value { value: copied },
            ..
        },
        CppStatement::Assign { target, value, .. },
        CppStatement::Return {
            value: returned, ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("caller did not retain declaration, local assignment, and return")
    };
    assert_eq!(captured.name, "captured");
    assert!(!captured.declaration_id.is_empty());
    assert_eq!(relayed.name, "relayed");
    assert_ne!(captured.declaration_id, relayed.declaration_id);
    assert_eq!(callee.declaration_id, reachable.declaration_id);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Reference { .. }]
    ));
    assert!(matches!(
        copied,
        CppExpression::Load { place, .. }
            if place.declaration_id == captured.declaration_id
    ));
    assert_eq!(target.declaration_id, relayed.declaration_id);
    assert!(matches!(
        value,
        CppExpression::Binary { left, .. }
            if matches!(left.as_ref(), CppExpression::Load { place, .. }
                if place.declaration_id == relayed.declaration_id)
    ));
    assert!(matches!(
        returned,
        CppExpression::Load { place, .. } if place.declaration_id == relayed.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower the scalar local through kernel statements");
    assert_eq!(
        contains_scalar_local_pipeline(
            lowered.kernel_function().body(),
            "captured",
            "relayed",
            "read_value"
        ),
        [true, true, true, true]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "relay_value.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the scalar-local caller proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded scalar-local proof must reverify");
    // Construction checks the same complete original and returns its claim metadata.
    let (session, verified) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &import)
            .expect("retain the scalar-local verification environment");
    assert_eq!(verified.len(), 5);

    let next = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "relay_value.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded local proof");

    let false_contract = SCALAR_LOCAL_SIDECAR.replace(
        "ensures result == value + 1;",
        "ensures result == value + 2;",
    );
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false claim about the captured call result must be rejected");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn mutable_pointer_dereference_and_reference_address_verify_offline() {
    let project = Project::pointer();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, POINTER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export pointer operations and the resolved call");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the pointer artifact offline");
    assert_eq!(import.export().schema, 61);
    let caller = &import.export().functions[0];
    assert_eq!(caller.name, "bump_reference");
    assert!(matches!(
        caller.parameters[0].value_type,
        CppType::LvalueReference { .. }
    ));
    let [helper] = import.export().reachable_functions.as_slice() else {
        panic!("the pointer helper was not captured")
    };
    assert_eq!(helper.name, "bump_pointer");
    assert!(matches!(
        helper.parameters[0].value_type,
        CppType::Pointer { ref pointee }
            if matches!(pointee.as_ref(), CppType::Integer {
                bits: 32,
                signed: true,
                is_const: false,
                ..
            })
    ));

    let [
        CppStatement::Declare {
            initializer: CppInitializer::Call {
                callee, arguments, ..
            },
            ..
        },
        CppStatement::Return { .. },
    ] = caller.body.as_slice()
    else {
        panic!("the reference caller did not retain its call-result local")
    };
    assert_eq!(callee.declaration_id, helper.declaration_id);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Value {
            value: CppExpression::AddressOf { place, value_type, .. }
        }] if place.declaration_id == caller.parameters[0].declaration_id
            && matches!(value_type, CppType::Pointer { .. })
    ));

    let [
        CppStatement::Store {
            pointer: stored_through,
            value: CppExpression::Binary {
                left: loaded_value, ..
            },
            ..
        },
        CppStatement::Return {
            value: returned_value,
            ..
        },
    ] = helper.body.as_slice()
    else {
        panic!("the pointer helper did not retain its checked load/store operations")
    };
    assert!(matches!(
        stored_through,
        CppExpression::Load { place, value_type, .. }
            if place.declaration_id == helper.parameters[0].declaration_id
                && matches!(value_type, CppType::Pointer { .. })
    ));
    assert!(matches!(
        loaded_value.as_ref(),
        CppExpression::Dereference { pointer, .. }
            if matches!(pointer.as_ref(), CppExpression::Load { place, .. }
                if place.declaration_id == helper.parameters[0].declaration_id)
    ));
    assert!(matches!(
        returned_value,
        CppExpression::Dereference { pointer, .. }
            if matches!(pointer.as_ref(), CppExpression::Load { place, .. }
                if place.declaration_id == helper.parameters[0].declaration_id)
    ));

    let lowered =
        lower_import(&import).expect("lower pointer operations through kernel memory rules");
    assert_eq!(
        lowered.kernel_function().parameters()[0].program_type(),
        ProgramType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[0].program_type(),
        ProgramType::Int32Pointer
    );
    assert!(!lowered.reachable_kernel_functions()[0].parameters()[0].pointee_is_constant());

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify pointer load/store and reference address through shared rules");
    assert_eq!(verified.len(), 6);

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "bump_reference.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the pointer caller proof");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded pointer proof must reverify");

    let missing_ownership = POINTER_SIDECAR.replacen("    owns pointer[0..1];\n", "", 1);
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_ownership_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_program_prepared_project(&missing_ownership_project, &import)
        .expect_err("dereferencing without memory authority must not verify");

    let false_contract = POINTER_SIDECAR.replace(
        "ensures value == old(value) + 1;",
        "ensures value == old(value) + 2;",
    );
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false pointer-mediated memory effect must be rejected");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn record_reference_member_loads_and_stores_verify_offline() {
    let project = Project::struct_member();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, STRUCT_MEMBER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the resolved C++ record layout and fields");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the record artifact offline");
    assert_eq!(import.export().schema, 61);
    let [record] = import.export().records.as_slice() else {
        panic!("the referenced record layout was not captured")
    };
    assert_eq!(record.name, "RestoreState");
    assert_eq!((record.size_bytes, record.alignment_bytes), (16, 8));
    let [pointer, saved] = record.fields.as_slice() else {
        panic!("the record fields were not captured")
    };
    assert_eq!(
        (
            pointer.name.as_str(),
            pointer.offset_bytes,
            pointer.size_bytes
        ),
        ("pointer", 0, 8)
    );
    assert!(matches!(pointer.value_type, CppType::Pointer { .. }));
    assert_eq!(
        (saved.name.as_str(), saved.offset_bytes, saved.size_bytes),
        ("saved", 8, 4)
    );
    assert!(matches!(saved.value_type, CppType::Integer { .. }));

    let function = &import.export().functions[0];
    assert!(matches!(
        &function.parameters[0].value_type,
        CppType::LvalueReference { pointee }
            if matches!(pointee.as_ref(), CppType::Record { name, declaration_id, .. }
                if name == "RestoreState" && declaration_id == &record.declaration_id)
    ));
    assert!(matches!(
        function.body.as_slice(),
        [
            CppStatement::MemberStore { field: first, .. },
            CppStatement::MemberStore { field: second, .. },
            CppStatement::Store {
                pointer: CppExpression::MemberLoad { field: third, .. },
                ..
            },
            CppStatement::Return {
                value: CppExpression::MemberLoad { field: fourth, .. },
                ..
            },
        ] if first.declaration_id == pointer.declaration_id
            && second.declaration_id == saved.declaration_id
            && third.declaration_id == pointer.declaration_id
            && fourth.declaration_id == saved.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower member operations through checked offsets");
    assert_eq!(
        lowered.kernel_function().parameters()[0].program_type(),
        ProgramType::Int32Pointer
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify field access and the loaded pointer through shared memory rules");
    assert_eq!(verified.len(), 7);

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "stage_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the record execution proof");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded record proof must reverify");

    let missing_ownership = STRUCT_MEMBER_SIDECAR.replace("    owns state.pointer;\n", "");
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("writing a field without its memory authority must not verify");

    let false_contract =
        STRUCT_MEMBER_SIDECAR.replace("ensures value == 7;", "ensures value == 8;");
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false pointer-mediated member effect must be rejected");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn brace_initialized_local_aggregate_verifies_offline() {
    let project = Project::local_aggregate();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, LOCAL_AGGREGATE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the local aggregate initializer");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the aggregate artifact offline");
    assert_eq!(import.export().schema, 61);
    let [record] = import.export().records.as_slice() else {
        panic!("the local aggregate record layout was not captured")
    };
    let [pointer, saved] = record.fields.as_slice() else {
        panic!("the local aggregate fields were not captured")
    };
    let [
        CppStatement::Declare {
            local,
            initializer: CppInitializer::Aggregate { fields, .. },
            ..
        },
        CppStatement::Store {
            pointer: CppExpression::MemberLoad { object, field, .. },
            ..
        },
        CppStatement::Return {
            value:
                CppExpression::MemberLoad {
                    object: returned_object,
                    field: returned_field,
                    ..
                },
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the local object did not retain initialization and member use")
    };
    assert!(matches!(
        &local.value_type,
        CppType::Record { declaration_id, name, .. }
            if declaration_id == &record.declaration_id && name == "RestoreState"
    ));
    assert!(matches!(
        fields.as_slice(),
        [first, second]
            if first.field.declaration_id == pointer.declaration_id
                && second.field.declaration_id == saved.declaration_id
                && matches!(first.value, CppExpression::AddressOf { .. })
                && matches!(second.value, CppExpression::Load { .. })
    ));
    assert_eq!(object.declaration_id, local.declaration_id);
    assert_eq!(field.declaration_id, pointer.declaration_id);
    assert_eq!(returned_object.declaration_id, local.declaration_id);
    assert_eq!(returned_field.declaration_id, saved.declaration_id);

    let lowered = lower_import(&import).expect("lower the local aggregate to checked stack memory");
    assert_eq!(
        contains_local_aggregate_pipeline(lowered.kernel_function().body(), "state"),
        [true, true, true]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify local aggregate initialization and later field reads");
    assert_eq!(verified.len(), 3);

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "stage_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the local aggregate execution proof");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded local aggregate proof must reverify");

    let missing_ownership = LOCAL_AGGREGATE_SIDECAR.replace("    owns value;\n", "");
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("the initializer and later pointer write require input memory authority");

    let false_contract =
        LOCAL_AGGREGATE_SIDECAR.replace("ensures result == old(value);", "ensures result == 7;");
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false claim about the saved initialized field must be rejected");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn explicit_constructor_local_verifies_as_a_modular_call() {
    let project = Project::constructor_local();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTRUCTOR_LOCAL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the direct constructor call and body");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the constructor artifact offline");
    assert_eq!(import.export().schema, 61);
    let [record] = import.export().records.as_slice() else {
        panic!("the constructed record layout was not captured")
    };
    let [constructor] = import.export().reachable_functions.as_slice() else {
        panic!("the resolved constructor definition was not exported")
    };
    assert!(matches!(
        &constructor.function_kind,
        CppFunctionKind::Constructor {
            record_declaration_id,
            record_name,
        } if record_declaration_id == &record.declaration_id
            && record_name == "RestoreState"
    ));
    assert_eq!(constructor.name, "RestoreState_constructor");
    assert_eq!(constructor.return_type, CppType::Void);
    assert!(matches!(
        constructor.parameters.as_slice(),
        [self_parameter, slot]
            if self_parameter.name == "self"
                && matches!(
                    &self_parameter.value_type,
                    CppType::LvalueReference { pointee }
                        if matches!(
                            pointee.as_ref(),
                            CppType::Record { declaration_id, .. }
                                if declaration_id == &record.declaration_id
                        )
                )
                && slot.name == "slot"
                && matches!(slot.value_type, CppType::Pointer { .. })
    ));
    assert!(matches!(
        constructor.body.as_slice(),
        [
            CppStatement::MemberStore { field: pointer, .. },
            CppStatement::MemberStore { field: saved, .. },
            CppStatement::Store {
                pointer: CppExpression::MemberLoad { field: used, .. },
                ..
            },
        ] if pointer.name == "pointer" && saved.name == "saved" && used.name == "pointer"
    ));

    let [
        CppStatement::Declare {
            local,
            initializer:
                CppInitializer::Constructor {
                    callee, arguments, ..
                },
            ..
        },
        CppStatement::Return { .. },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the direct object construction was not retained")
    };
    assert_eq!(local.name, "state");
    assert_eq!(callee.declaration_id, constructor.declaration_id);
    assert_eq!(callee.name, constructor.name);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Value {
            value: CppExpression::AddressOf { .. }
        }]
    ));

    let lowered = lower_import(&import).expect("lower construction through the shared call rules");
    assert!(contains_raw_aggregate_destination(
        lowered.kernel_function().body(),
        "state"
    ));
    assert!(contains_call(
        lowered.kernel_function().body(),
        "RestoreState::RestoreState"
    ));
    assert_eq!(lowered.reachable_kernel_functions().len(), 1);
    assert_eq!(
        lowered.reachable_kernel_functions()[0]
            .contract_interface()
            .construction_parameter()
            .map(|(index, _)| index),
        Some(0),
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[0].program_type(),
        ProgramType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[1].program_type(),
        ProgramType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].return_type(),
        ProgramType::Void
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify the constructor body and its implicit local invocation modularly");

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "capture.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the caller proof across construction");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded constructor caller proof must reverify");

    let missing_field_ownership = CONSTRUCTOR_LOCAL_SIDECAR.replace("    owns this->saved;\n", "");
    fs::write(&sidecar, &missing_field_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_field_ownership).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("constructor member initialization requires field authority");

    let false_constructor_contract = CONSTRUCTOR_LOCAL_SIDECAR.replace(
        "ensures this->saved == old(slot[0]);",
        "ensures this->saved == old(slot[0]) + 1;",
    );
    fs::write(&sidecar, &false_constructor_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_constructor_contract).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false constructor field effect must be rejected");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn terminal_return_captures_value_before_checked_destructor_cleanup() {
    let project = Project::terminal_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, TERMINAL_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export constructor and terminal destructor cleanup");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the cleanup artifact offline");
    assert_eq!(import.export().schema, 61);
    let [record] = import.export().records.as_slice() else {
        panic!("the destructible record layout was not captured")
    };
    let destructor_reference = record
        .destructor
        .as_ref()
        .expect("the record must retain its declared destructor identity");
    let constructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Constructor { .. }))
        .expect("constructor definition must be reachable");
    let destructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Destructor { .. }))
        .expect("destructor definition must be reachable");
    assert_eq!(
        destructor_reference.declaration_id,
        destructor.declaration_id
    );
    assert_eq!(destructor_reference.name, "RestoreState_destructor");
    assert!(matches!(
        &destructor.function_kind,
        CppFunctionKind::Destructor {
            record_declaration_id,
            record_name,
        } if record_declaration_id == &record.declaration_id
            && record_name == "RestoreState"
    ));
    assert_eq!(destructor.return_type, CppType::Void);
    assert!(matches!(
        destructor.parameters.as_slice(),
        [self_parameter] if self_parameter.name == "self"
    ));
    assert!(matches!(
        destructor.body.as_slice(),
        [CppStatement::Store {
            pointer: CppExpression::MemberLoad { field: pointer, .. },
            value: CppExpression::MemberLoad { field: saved, .. },
            ..
        }] if pointer.name == "pointer" && saved.name == "saved"
    ));

    let [
        CppStatement::Declare {
            local,
            initializer: CppInitializer::Constructor { callee, .. },
            ..
        },
        CppStatement::Return {
            cleanups,
            value: CppExpression::Load { .. },
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the terminal cleanup edge was not retained")
    };
    assert_eq!(local.name, "state");
    assert_eq!(callee.declaration_id, constructor.declaration_id);
    assert!(matches!(
        cleanups.as_slice(),
        [CppCleanup::Destructor {
            object,
            callee,
            ..
        }] if object.declaration_id == local.declaration_id
            && callee.declaration_id == destructor.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower return capture and destructor cleanup");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        ["RestoreState::RestoreState", "RestoreState::~RestoreState"]
    );
    assert!(matches!(
        lowered.kernel_function().body(),
        ProgramStatement::Seq(sequence)
            if matches!(
                sequence.iter().last().map(|stmt| stmt.as_ref()),
                Some(ProgramStatement::Return(ProgramExpression::StepResult {
                    origin: click::kernel::StepOrigin::Value(_),
                    ends: true,
                    ..
                }))
            )
    ));

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify captured result and restored caller memory");

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "capture.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the proof across terminal cleanup");
    assert!(!expanded.contains("__click_cpp_return_value"), "{expanded}");
    assert!(!expanded.contains("__click_cpp_nested_value"), "{expanded}");
    assert!(
        !expanded.contains("__click_cpp_unwind_exception"),
        "{expanded}"
    );
    assert!(!expanded.contains(".temporary("), "{expanded}");
    click::surface::without_implicit_solve_for_claim("capture.contract", || {
        verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
            .map_err(|error| error.report())
    })
    .expect("expanded terminal-cleanup proof must cold reverify");

    let missing_destructor = TERMINAL_DESTRUCTOR_SIDECAR.replace(
        "RestoreState::~RestoreState() {\n    requires separate(memory(*this), memory(this->pointer[0..1]));\n    owns this->pointer;\n    owns this->saved;\n    owns this->pointer[0..1];\n    ensures this->pointer == old(this->pointer);\n    ensures this->saved == old(this->saved);\n    ensures this->pointer[0] == old(this->saved);\n}\n\n",
        "",
    );
    fs::write(&sidecar, &missing_destructor).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_destructor).unwrap();
    verify_program_prepared_project(&missing_project, &import)
        .expect_err("implicit cleanup requires a checked destructor contract");

    let false_destructor = TERMINAL_DESTRUCTOR_SIDECAR.replace(
        "ensures this->pointer[0] == old(this->saved);",
        "ensures this->pointer[0] == old(this->saved) + 1;",
    );
    fs::write(&sidecar, &false_destructor).unwrap();
    let false_project = read_click_project(&sidecar, &false_destructor).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a false destructor restore effect must be rejected");

    let wrong_capture = TERMINAL_DESTRUCTOR_SIDECAR
        .replace("ensures result == 7;", "ensures result == old(value);");
    fs::write(&sidecar, &wrong_capture).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_capture).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("the return value must be captured before destruction");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: C++ early void return proof and replay"]
fn cpp_void_early_return_skips_following_statements() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/cpp-verification/void-early-return");
    let cpp = fs::read_to_string(fixture.join("advance.cpp")).unwrap();
    let project = Project::with_fixture("advance.cpp", "advance", &cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [CppStatement::If { then_branch, .. }, _] = import.export().functions[0].body.as_slice()
    else {
        panic!("expected the early exit and the following cursor write");
    };
    assert!(matches!(
        then_branch.as_slice(),
        [CppStatement::ReturnVoid { cleanups, .. }] if cleanups.is_empty()
    ));
    let source = fs::read_to_string(fixture.join("advance.click")).unwrap();
    check_selected_claim_certificate(&project, &import, &source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: C++ void return with checked cleanup on both paths"]
fn cpp_void_early_return_runs_destructors() {
    let cpp = EARLY_RETURN_DESTRUCTOR_SOURCE
        .replace("int with_restore(", "void with_restore(")
        .replace("return value;", "return;");
    let project = Project::with_fixture("with_restore.cpp", "with_restore", &cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [
        CppStatement::Declare { local, .. },
        CppStatement::If { then_branch, .. },
        _,
        CppStatement::ReturnVoid {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("expected destruction on both return edges");
    };
    let [
        CppStatement::ReturnVoid {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("expected a value-free early return");
    };
    for cleanups in [early_cleanups, final_cleanups] {
        assert!(matches!(
            cleanups.as_slice(),
            [CppCleanup::Destructor { object, .. }] if object.declaration_id == local.declaration_id
        ));
    }
    let source = EARLY_RETURN_DESTRUCTOR_SIDECAR
        .replace("int32 with_restore(", "void with_restore(")
        .replace("    ensures early implies result == 7;\n", "")
        .replace("    ensures not early implies result == 9;\n", "");
    check_selected_claim_certificate(&project, &import, &source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn every_return_after_construction_runs_the_checked_destructor() {
    let project = Project::early_return_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, EARLY_RETURN_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export cleanup on both C++ return edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the cleanup artifact offline");
    assert_eq!(import.export().schema, 61);
    let destructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Destructor { .. }))
        .expect("destructor definition must be reachable");
    let [
        CppStatement::Declare { local, .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the two cleanup-bearing return paths were not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the early return edge was not retained")
    };
    for cleanups in [early_cleanups, final_cleanups] {
        assert!(matches!(
            cleanups.as_slice(),
            [CppCleanup::Destructor {
                object,
                callee,
                ..
            }] if object.declaration_id == local.declaration_id
                && callee.declaration_id == destructor.declaration_id
        ));
    }

    let lowered = lower_import(&import).expect("lower cleanup on both return edges");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        ["Restore::Restore", "Restore::~Restore", "Restore::~Restore"]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify both captured results and both restored-memory paths");
    let ensure_indices = verified
        .iter()
        .map(|theorem| match theorem.claim {
            VerifiedClaim::Ensure { index, .. } => index,
            VerifiedClaim::ExceptionalEnsure { index, .. } => index,
        })
        .collect::<Vec<_>>();
    assert!(
        ensure_indices.ends_with(&[0, 1, 2, 3, 0, 1, 2, 3]),
        "both caller return paths must certify ownership, the captured result, and restoration: {ensure_indices:?}"
    );

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "with_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both cleanup edges");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded early-return cleanup proof must reverify");

    let wrong_early_result = EARLY_RETURN_DESTRUCTOR_SIDECAR.replace(
        "ensures early implies result == 7;",
        "ensures early implies result == 9;",
    );
    assert_ne!(wrong_early_result, EARLY_RETURN_DESTRUCTOR_SIDECAR);
    fs::write(&sidecar, &wrong_early_result).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_early_result).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("cleanup must not overwrite the value captured by the early return");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn modular_caller_observes_captured_result_and_restored_entry_value() {
    assert!(
        RESTORE_CALLER_SOURCE.starts_with(EARLY_RETURN_DESTRUCTOR_SOURCE),
        "the caller fixture must preserve the original RAII source verbatim"
    );
    let project = Project::restore_caller();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, RESTORE_CALLER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the RAII helper and its modular caller");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the caller artifact offline");
    assert_eq!(import.export().functions[0].name, "call_with_restore");
    assert!(
        import
            .export()
            .reachable_functions
            .iter()
            .any(|function| function.name == "with_restore"),
        "the helper definition must be reachable from the selected caller"
    );
    let CppStatement::Declare {
        initializer: CppInitializer::Call { callee, .. },
        ..
    } = &import.export().functions[0].body[0]
    else {
        panic!("the caller must capture a resolved call result")
    };
    assert_eq!(callee.name, "with_restore");
    let lowered = lower_import(&import).expect("lower the modular RAII call");
    assert!(
        contains_scalar_local_pipeline(
            lowered.kernel_function().body(),
            "captured",
            "unused",
            "with_restore"
        )[..2]
            .iter()
            .all(|found| *found),
        "the captured call must retain its result before assigning it"
    );

    let click_project = read_click_project(&sidecar, RESTORE_CALLER_SIDECAR).unwrap();
    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "call_with_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the caller's checked modular execution");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded RAII caller proof must reverify");
    // Session construction cold-verifies this complete program once.
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &import)
            .expect("retain the caller's original verification environment");
    let next = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "call_with_restore.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded RAII caller proof");

    let false_restoration =
        RESTORE_CALLER_SIDECAR.replace("ensures value == 41;", "ensures value == 42;");
    fs::write(&sidecar, &false_restoration).unwrap();
    let false_project = read_click_project(&sidecar, &false_restoration).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("the caller cannot claim a different post-call value");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn two_constructed_objects_are_destroyed_in_reverse_order_on_every_return() {
    let project = Project::reverse_destructor_order();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, REVERSE_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export reverse cleanup on both C++ return edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the ordered cleanup artifact offline");
    assert_eq!(import.export().schema, 61);
    let [
        CppStatement::Declare { local: first, .. },
        CppStatement::Declare { local: second, .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the two constructed objects and return edges were not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the early return edge was not retained")
    };
    assert_eq!(first.name, "first");
    assert_eq!(second.name, "second");
    for cleanups in [early_cleanups, final_cleanups] {
        let [
            CppCleanup::Destructor {
                object: second_cleanup,
                ..
            },
            CppCleanup::Destructor {
                object: first_cleanup,
                ..
            },
        ] = cleanups.as_slice()
        else {
            panic!("each return must retain two destructor calls")
        };
        assert_eq!(second_cleanup.declaration_id, second.declaration_id);
        assert_eq!(first_cleanup.declaration_id, first.declaration_id);
    }

    let lowered = lower_import(&import).expect("lower both reversed cleanup lists");
    assert_eq!(
        destructor_object_order(lowered.kernel_function().body(), "Restore::~Restore"),
        ["second", "first", "second", "first"]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify both return values and reverse-order restoration");

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "restore_twice.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both ordered cleanup lists");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded reverse-cleanup proof must reverify");

    let growing = Project::reverse_destructor_order();
    fs::write(
        growing.source(),
        REVERSE_DESTRUCTOR_SOURCE.replace(
            "Restore second(&value);",
            "Restore second(&value);\n    Restore third(&value);",
        ),
    )
    .unwrap();
    refresh_import(&growing.config()).expect("a third destructible local is supported");
    let growing_import = load_import(&growing.config()).unwrap();
    assert_eq!(
        destructor_object_order(
            lower_import(&growing_import)
                .unwrap()
                .kernel_function()
                .body(),
            "Restore::~Restore"
        ),
        ["third", "second", "first", "third", "second", "first"]
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn nested_scope_destroys_its_object_on_return_and_fallthrough() {
    let project = Project::nested_scope_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, NESTED_SCOPE_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export both nested-scope cleanup edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the nested-scope artifact offline");
    assert_eq!(import.export().schema, 61);
    let destructor = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| matches!(function.function_kind, CppFunctionKind::Destructor { .. }))
        .expect("destructor definition must be reachable");
    let [
        CppStatement::Scope {
            body,
            cleanups: fallthrough_cleanups,
            ..
        },
        CppStatement::Return {
            cleanups: outer_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the lexical cleanup boundary was not retained")
    };
    let [
        CppStatement::Declare { local, .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
    ] = body.as_slice()
    else {
        panic!("the nested block body was not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the nested early return was not retained")
    };
    assert!(outer_cleanups.is_empty());
    for cleanups in [early_cleanups, fallthrough_cleanups] {
        assert!(matches!(
            cleanups.as_slice(),
            [CppCleanup::Destructor {
                object,
                callee,
                ..
            }] if object.declaration_id == local.declaration_id
                && callee.declaration_id == destructor.declaration_id
        ));
    }

    let lowered = lower_import(&import).expect("lower the lexical cleanup boundary directly");
    assert_eq!(
        destructor_object_order(lowered.kernel_function().body(), "Restore::~Restore"),
        ["guard", "guard"]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify early exit and normal exit from the nested scope");

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "scoped_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both nested-scope cleanup edges");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded nested-scope proof must reverify");

    let wrong_fallthrough = NESTED_SCOPE_DESTRUCTOR_SIDECAR.replace(
        "ensures early == false implies result == old(value);",
        "ensures early == false implies result == 9;",
    );
    fs::write(&sidecar, &wrong_fallthrough).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_fallthrough).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("fallthrough destruction must occur before the outer return");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 8s in the parallel gate"]
fn sibling_scopes_reuse_a_local_name_with_independent_cleanup() {
    let project = Project::sibling_scope_destructors();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIBLING_SCOPE_DESTRUCTORS_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export both sibling cleanup scopes");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the sibling-scope artifact offline");
    let [
        CppStatement::Scope {
            body: first_body,
            cleanups: first_fallthrough,
            ..
        },
        CppStatement::Scope {
            body: second_body,
            cleanups: second_fallthrough,
            ..
        },
        CppStatement::Return {
            cleanups: outer_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the two sibling lifetime boundaries were not retained")
    };
    let [
        CppStatement::Declare {
            local: first_local, ..
        },
        CppStatement::If {
            then_branch: first_then,
            ..
        },
        CppStatement::Assign { .. },
    ] = first_body.as_slice()
    else {
        panic!("the first sibling scope was not retained")
    };
    let [
        CppStatement::Declare {
            local: second_local,
            ..
        },
        CppStatement::If {
            then_branch: second_then,
            ..
        },
        CppStatement::Assign { .. },
    ] = second_body.as_slice()
    else {
        panic!("the second sibling scope was not retained")
    };
    assert_eq!(first_local.name, "guard");
    assert_eq!(second_local.name, "guard");
    assert_ne!(first_local.declaration_id, second_local.declaration_id);
    assert!(outer_cleanups.is_empty());
    for (local, branch, fallthrough) in [
        (first_local, first_then, first_fallthrough),
        (second_local, second_then, second_fallthrough),
    ] {
        let [
            CppStatement::Return {
                cleanups: return_cleanups,
                ..
            },
        ] = branch.as_slice()
        else {
            panic!("a sibling scope lost its early return")
        };
        for cleanups in [return_cleanups, fallthrough] {
            assert!(matches!(
                cleanups.as_slice(),
                [CppCleanup::Destructor { object, .. }]
                    if object.declaration_id == local.declaration_id
                        && object.name == local.name
            ));
        }
    }

    let lowered = lower_import(&import).expect("lower the sibling lexical lifetimes directly");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        [
            "Restore::Restore",
            "Restore::~Restore",
            "Restore::~Restore",
            "Restore::Restore",
            "Restore::~Restore",
            "Restore::~Restore",
        ]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify independent cleanup and restoration in both sibling scopes");

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "sibling_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the proof across both sibling lifetime boundaries");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded sibling-scope proof must reverify");

    let wrong_final = SIBLING_SCOPE_DESTRUCTORS_SIDECAR.replace(
        "second_early == false implies result == old(value)",
        "second_early == false implies result == 11",
    );
    fs::write(&sidecar, &wrong_final).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_final).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("the second scope must clean up before the final outer return");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 8s in the parallel gate"]
fn third_sibling_scope_preserves_independent_cleanup_and_frames() {
    let growing = Project::sibling_scope_destructors();
    fs::write(
        growing.source(),
        SIBLING_SCOPE_DESTRUCTORS_SOURCE.replace(
            "    return value;\n}",
            "    {\n        Restore guard(&value);\n        value = 13;\n    }\n    return value;\n}",
        ),
    )
    .unwrap();
    refresh_import(&growing.config()).expect("a third sibling scope is supported");
    let growing_import = load_import(&growing.config()).unwrap();
    assert_eq!(
        growing_import.export().functions[0]
            .body
            .iter()
            .filter(|statement| matches!(statement, CppStatement::Scope { .. }))
            .count(),
        3
    );
    check_selected_claim_certificate(&growing, &growing_import, SIBLING_SCOPE_DESTRUCTORS_SIDECAR);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn overlapping_scope_destroys_inner_before_outer_on_every_exit() {
    let project = Project::overlapping_scope_destructors();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, OVERLAPPING_SCOPE_DESTRUCTORS_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export overlapping cleanup lifetimes");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import =
        load_import(&project.config()).expect("load the overlapping-scope artifact offline");
    let [
        CppStatement::Declare {
            local: outer_local, ..
        },
        CppStatement::Scope {
            body: inner_body,
            cleanups: inner_fallthrough,
            ..
        },
        CppStatement::Declare { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the overlapping lexical cleanup boundary was not retained")
    };
    let [
        CppStatement::Declare {
            local: inner_local, ..
        },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
    ] = inner_body.as_slice()
    else {
        panic!("the inner cleanup scope body was not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the overlapping early return was not retained")
    };
    assert_eq!(outer_local.name, "outer");
    assert_eq!(inner_local.name, "inner");
    assert!(matches!(
        inner_fallthrough.as_slice(),
        [CppCleanup::Destructor { object, .. }]
            if object.declaration_id == inner_local.declaration_id
    ));
    assert!(matches!(
        early_cleanups.as_slice(),
        [
            CppCleanup::Destructor {
                object: inner_object,
                ..
            },
            CppCleanup::Destructor {
                object: outer_object,
                ..
            },
        ] if inner_object.declaration_id == inner_local.declaration_id
            && outer_object.declaration_id == outer_local.declaration_id
    ));
    assert!(matches!(
        final_cleanups.as_slice(),
        [CppCleanup::Destructor { object, .. }]
            if object.declaration_id == outer_local.declaration_id
    ));

    let lowered = lower_import(&import).expect("lower the overlapping lifetimes directly");
    assert_eq!(
        destructor_object_order(lowered.kernel_function().body(), "Restore::~Restore"),
        ["inner", "outer", "inner", "outer"]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("verify inner-then-outer cleanup and memory restoration");

    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "overlap_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the proof across overlapping cleanup lifetimes");
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded overlapping-cleanup proof must reverify");

    let wrong_result = OVERLAPPING_SCOPE_DESTRUCTORS_SIDECAR
        .replace("ensures result == 7;", "ensures result == 11;");
    fs::write(&sidecar, &wrong_result).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_result).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("inner fallthrough cleanup must restore 7 before the final return");
}

#[test]
fn overlapping_scope_rejects_shadowing_and_a_second_inner_lifetime() {
    for (source, expected) in [
        (
            OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE.replace("Restore inner", "Restore outer"),
            "shadows another supported place",
        ),
        (
            OVERLAPPING_SCOPE_DESTRUCTORS_SOURCE.replace(
                "    int observed = value;",
                "    {\n        Restore later(&value);\n        value = 13;\n    }\n    int observed = value;",
            ),
            "permits one inner cleanup scope with an outer object",
        ),
    ] {
        let project = Project::overlapping_scope_destructors();
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn conditional_construction_cleans_up_only_the_constructed_arm() {
    let project = Project::conditional_construction();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONDITIONAL_CONSTRUCTION_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the conditional object lifetime");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import =
        load_import(&project.config()).expect("load the conditional-construction artifact offline");
    let [
        CppStatement::If {
            then_branch,
            else_branch,
            ..
        },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("the conditional lifetime boundary was not retained")
    };
    let [
        CppStatement::Scope {
            body,
            cleanups: fallthrough_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("the constructed arm was not retained as a cleanup scope")
    };
    let [
        CppStatement::Declare { local, .. },
        CppStatement::If {
            then_branch: early_branch,
            ..
        },
        CppStatement::Assign { .. },
    ] = body.as_slice()
    else {
        panic!("the conditional cleanup scope body was not retained")
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = early_branch.as_slice()
    else {
        panic!("the constructed arm's early return was not retained")
    };
    assert!(else_branch.is_empty());
    assert!(final_cleanups.is_empty());
    for cleanups in [early_cleanups, fallthrough_cleanups] {
        assert!(matches!(
            cleanups.as_slice(),
            [CppCleanup::Destructor { object, .. }]
                if object.declaration_id == local.declaration_id
                    && object.name == "guard"
        ));
    }

    let lowered = lower_import(&import).expect("lower the conditional lifetime directly");
    assert_eq!(
        call_order(lowered.kernel_function().body()),
        ["Restore::Restore", "Restore::~Restore", "Restore::~Restore",]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();

    let expanded = expand_project_claim_source_by_label(
        &click_project,
        &ProgramInputs::program(&import),
        "conditional_restore.contract",
    )
    .expect("fully expand the proof across the conditional lifetime");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the fully expanded conditional-construction proof must reverify");
    // Session construction cold-verifies this complete program once.
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &import)
            .expect("retain the original conditional-construction verification environment");
    let next = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "conditional_restore.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit must verify the fully expanded cleanup proof");

    let false_restoration =
        CONDITIONAL_CONSTRUCTION_SIDECAR.replace("ensures value == 41;", "ensures value == 42;");
    let false_project = read_click_project(&sidecar, &false_restoration).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("the caller cannot claim a different restored value");

    let wrong_skipped_result = CONDITIONAL_CONSTRUCTION_SIDECAR.replace(
        "ensures construct == false implies result == 41;",
        "ensures construct == false implies result == 7;",
    );
    fs::write(&sidecar, &wrong_skipped_result).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_skipped_result).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("the skipped-construction path must return the untouched input");
}

#[test]
fn conditional_construction_rejects_both_arms_outer_objects_and_deeper_objects() {
    for (source, expected) in [
        (
            CONDITIONAL_CONSTRUCTION_SOURCE.replace(
                "        value = 9;\n    }\n    return value;",
                "        value = 9;\n    } else {\n        Restore other(&value);\n        value = 11;\n    }\n    return value;",
            ),
            "exactly one cleanup scope in one if arm",
        ),
        (
            CONDITIONAL_CONSTRUCTION_SOURCE.replace(
                "int conditional_restore(bool construct, bool early, int& value) noexcept {\n    if (construct)",
                "int conditional_restore(bool construct, bool early, int& value) noexcept {\n    Restore outer(&value);\n    if (construct)",
            ),
            "conditional construction cannot yet be combined with an outer aggregate object",
        ),
        (
            CONDITIONAL_CONSTRUCTION_SOURCE.replace(
                "        Restore guard(&value);",
                "        if (early) {\n            Restore nested(&value);\n        }\n        Restore guard(&value);",
            ),
            "automatic C++ locals are currently supported only in the function body",
        ),
    ] {
        let project = Project::conditional_construction();
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn nested_scope_rejects_conditional_construction_and_deeper_blocks() {
    for (source, expected) in [
        (
            NESTED_SCOPE_DESTRUCTOR_SOURCE.replace(
                "        Restore guard(&value);\n        if (early) {\n            return value;\n        }\n        value = 9;",
                "        if (early) {\n            Restore guard(&value);\n        }",
            ),
            "automatic C++ locals are currently supported only in the function body",
        ),
        (
            NESTED_SCOPE_DESTRUCTOR_SOURCE.replace(
                "        Restore guard(&value);",
                "        {\n            Restore guard(&value);\n        }",
            ),
            "permits one nested scope directly in a free-function body",
        ),
    ] {
        let project = Project::nested_scope_destructor();
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("scoped_restore.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn constructor_local_rejects_throwing_partial_and_reordered_forms() {
    let project = Project::constructor_local();
    for (source, expected) in [
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    explicit RestoreState(int* slot) : pointer(slot), saved(*slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "public non-default noexcept constructor",
        ),
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    explicit RestoreState(int* slot) noexcept : pointer(slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "explicitly initialize every field",
        ),
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    explicit RestoreState(int* slot) noexcept : saved(*slot), pointer(slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "initializer list must follow declaration order",
        ),
    ] {
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("capture.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn terminal_destructor_rejects_throwing_empty_and_nonterminal_cleanup() {
    let project = Project::terminal_destructor();
    for (source, expected) in [
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "~RestoreState() noexcept",
                "~RestoreState() noexcept(false)",
            ),
            "public, non-virtual outside a polymorphic class, non-deleted, and explicitly noexcept",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace("~RestoreState() noexcept", "~RestoreState()"),
            "public, non-virtual outside a polymorphic class, non-deleted, and explicitly noexcept",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "~RestoreState() noexcept {\n        *pointer = saved;\n    }",
                "~RestoreState() noexcept {}",
            ),
            "nonempty destructor body",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "return value;",
                "int result = value;\n    return result;\n    value = 9;",
            ),
            "requires one final return",
        ),
    ] {
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("capture.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn cpp_local_aggregate_rejects_partial_default_copy_nested_and_second_objects() {
    let project = Project::local_aggregate();

    for (source, expected) in [
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value) noexcept {\n    RestoreState state{&value};\n    return value;\n}\n",
            "one direct brace initializer per field",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value) noexcept {\n    RestoreState state;\n    return value;\n}\n",
            "one direct brace initializer per field",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(RestoreState& original, int& value) noexcept {\n    RestoreState copied = original;\n    return value;\n}\n",
            "one direct brace initializer per field",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value, bool condition) noexcept {\n    if (condition) { RestoreState state{&value, value}; }\n    return value;\n}\n",
            "only in the function body",
        ),
        (
            "struct RestoreState { int* pointer; int saved; };\nint stage_restore(int& value) noexcept {\n    RestoreState first{&value, value};\n    RestoreState second{&value, value};\n    return value;\n}\n",
            "multiple aggregate objects only when all require destruction",
        ),
    ] {
        fs::write(project.source(), source).unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("stage_restore.cpp"), "{error}");
        assert!(error.contains(expected), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn cpp_native_pointer_offsets_preserve_index_width_and_range_authority() {
    for (cpp_type, click_type, index, expression, expected) in [
        ("int", "int32", "1", "data + index", "1"),
        ("int", "int32", "-1", "(data + 2) + index", "1"),
        ("unsigned int", "uint32", "1u32", "index + data", "1"),
        ("long", "int64", "1i64", "data + index", "1"),
        ("int", "int32", "1", "(data + 2) - index", "1"),
        ("unsigned long", "uint64", "2u64", "data + index", "2"),
    ] {
        let project = Project::with_fixture(
            "offset.cpp",
            "read",
            &format!(
                "int read(int* data, {cpp_type} index) noexcept {{ return *({expression}); }}"
            ),
        );
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = format!(
            r#"verifying "offset.cpp";
int32 read(int32* data, {click_type} index) {{
 owns data[0..3]; requires index == {index};
 ensures result == old(data[{expected}]);
 ensures data[0] == old(data[0]); ensures data[2] == old(data[2]);
}}
"#
        );
        check_selected_claim_certificate(&project, &import, &sidecar);
        let hostile = sidecar.replace(" owns data[0..3];", "");
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn cpp_native_size_t_last_load_checks_nonempty_and_actual_backing_bounds() {
    let project = Project::with_fixture(
        "last.cpp",
        "last",
        "int last(int* data, unsigned long length) noexcept { return *(data + (length - 1UL)); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let fixed_index = r#"verifying "last.cpp";
int32 last(int32* data, uint64 length) {
 owns data[0..1]; requires length == 1u64;
 ensures result == old(data[0]);
}
"#;
    check_first_claim_certificate(&project, &import, fixed_index);
    let unresolved = fixed_index
        .replace(
            "owns data[0..1];",
            "owns data[0]; views data[length - 1u64];",
        )
        .replace("requires length == 1u64;", "");
    let path = project.directory.join("unresolved.click");
    fs::write(&path, &unresolved).unwrap();
    let parsed = read_click_project(&path, &unresolved).unwrap();
    let error = match verify_program_prepared_project(&parsed, &import) {
        Err(error) => error,
        Ok(_) => panic!("an unfixed index cannot establish the first element's value"),
    };
    let message = error.message();
    assert!(message.contains("index/address"), "{message}");
    assert!(!message.contains("the store to"), "{message}");
    assert!(
        !message.contains("state `(length - 1u64) != 0`"),
        "{message}"
    );
    for (length, end, expected) in [("1u64", "1", "0"), ("3u64", "3", "2")] {
        let sidecar = format!(
            r#"verifying "last.cpp";
int32 last(int32* data, uint64 length) {{
 owns data[0..{end}]; requires length == {length};
 ensures result == old(data[{expected}]);
}}
"#
        );
        check_first_claim_certificate(&project, &import, &sidecar);
    }
    for (length, end) in [
        ("0u64", "1"),
        ("4u64", "3"),
        ("18446744073709551615u64", "3"),
    ] {
        let sidecar = format!(
            r#"verifying "last.cpp";
int32 last(int32* data, uint64 length) {{
 owns data[0..{end}]; requires length == {length}; ensures 0 == 0;
}}
"#
        );
        let path = project.directory.join("bad.click");
        fs::write(&path, &sidecar).unwrap();
        let parsed = read_click_project(&path, &sidecar).unwrap();
        assert!(
            verify_program_prepared_project(&parsed, &import).is_err(),
            "invalid length {length} must fail even under a trivial postcondition"
        );
    }
}

#[test]
fn cpp_pointer_offsets_reject_unmodelled_wide_subtraction_and_wider_indices() {
    for (source, diagnostic) in [
        (
            "int read(int* data, long index) noexcept { return *(data - index); }",
            "pointer subtraction currently requires an int32 index",
        ),
        (
            "int read(int* data, unsigned int index) noexcept { return *(data - index); }",
            "pointer subtraction currently requires an int32 index",
        ),
        (
            "int read(int* data, unsigned __int128 index) noexcept { return *(data + index); }",
            "pointer arithmetic requires a 32/64-bit integer index",
        ),
    ] {
        let project = Project::with_fixture("offset.cpp", "read", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
fn cpp_pointer_slice_rejects_differences_and_multilevel_pointers() {
    let project = Project::pointer();

    fs::write(
        project.source(),
        "int bump_reference(int* pointer) noexcept {\n    return (int)(pointer - pointer);\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:2"), "{error}");
    assert!(error.contains("pointer arithmetic"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int bump_reference(int** pointer) noexcept {\n    return **pointer;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:1"), "{error}");
    assert!(error.contains("native element pointer"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn cpp_record_slice_rejects_unresolved_methods_bitfields_and_inheritance() {
    let project = Project::struct_member();

    fs::write(
        project.source(),
        "struct RestoreState {\n    int saved;\n    int read();\n};\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    state.read();\n    return state.saved;\n}\n",
    )
    .unwrap();
    // A method another translation unit defines is exported as its
    // interface; one that may throw is refused.
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("must be noexcept"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct RestoreState {\n    int saved : 4;\n};\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    return state.saved;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("stage_restore.cpp:2"), "{error}");
    assert!(error.contains("without bit-fields"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct Base { int base; };\nstruct RestoreState : Base { int saved; };\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    return state.saved;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("stage_restore.cpp:2"), "{error}");
    assert!(error.contains("no own fields"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct First { int value; };\nstruct Second { int value; };\n\nint stage_restore(First& first, Second& second) noexcept {\n    first.value = second.value;\n    return first.value;\n}\n",
    )
    .unwrap();
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().records.len(), 2);
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "stage_restore.cpp";
int32 stage_restore(struct First& first, struct Second& second) {
 owns first.value; owns second.value;
 ensures result == old(second.value); ensures first.value == old(second.value);
}
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn cpp_profile_expansion_and_audit_session_share_the_locked_input() {
    let project = Project::new();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIDECAR).unwrap();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();

    let sites = project_smart_tactic_source_sites(&click_project, &ProgramInputs::program(&import))
        .unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec![click::instrumentation::IMPLICIT_TAIL_TACTIC]
    );
    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "increment.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .unwrap();
    assert_ne!(expanded, click_source);
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).expect("expanded proof must reverify");

    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&click_project, &import)
            .expect("start the retained audit session");
    let next = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        "increment.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained session must verify the rewritten C++ proof");
}

#[test]
fn cpp_sidecar_reports_source_and_signature_mismatches_without_c_fallback() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();

    let wrong_source = SIDECAR.replace("increment.cpp", "other.cpp");
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &wrong_source).unwrap();
    let click_project = read_click_project(&sidecar, &wrong_source).unwrap();
    let error = verify_program_prepared_project(&click_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("prepared C++ import logical source must exactly match"),
        "{}",
        error.message()
    );

    let wrong_signature = SIDECAR.replace("int32& value", "uint32& value");
    fs::write(&sidecar, &wrong_signature).unwrap();
    let click_project = read_click_project(&sidecar, &wrong_signature).unwrap();
    let error = verify_program_prepared_project(&click_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("signature mismatch for `increment` parameter 1"),
        "{}",
        error.message()
    );
}

#[test]
fn cpp_written_self_is_an_ordinary_parameter() {
    for (selected, native, sidecar) in [
        (
            "probe",
            "int probe(int self) noexcept { return self; }",
            "int32 probe(int32 self) { ensures result == self; }",
        ),
        (
            "Box::read",
            "struct Box { int value; int read(int self) const noexcept { return self; } };",
            "int32 Box::read(int32 self) const { ensures result == self; }",
        ),
    ] {
        let project = Project::with_fixture("driver.cpp", selected, native);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!("verifying \"driver.cpp\";\n{sidecar}");
        let path = project.directory.join("probe.click");
        fs::write(&path, &source).unwrap();
        let parsed = read_click_project(&path, &source).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .unwrap_or_else(|error| panic!("{}", error.report()));
    }
}

/// A reference parameter is declared as a reference and named as its
/// referent. Each older or mistaken spelling is refused with the one to
/// write.
#[test]
fn cpp_reference_parameters_are_declared_and_named_as_their_referents() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = project.directory.join("demo.click");
    let refusal = |source: &str| {
        assert_ne!(source, SIDECAR, "the mutation must change the sidecar");
        fs::write(&sidecar, source).unwrap();
        match read_click_project(&sidecar, source) {
            Err(error) => format!("{error:?}"),
            Ok(click_project) => {
                let error = verify_program_prepared_project(&click_project, &import)
                    .expect_err("the mutated sidecar must be refused");
                error.message().to_string()
            }
        }
    };

    let as_pointer = refusal(&SIDECAR.replace("int32& value", "int32* value"));
    assert!(
        as_pointer.contains(".click has Int32Pointer value, C has Int32& value"),
        "{as_pointer}"
    );
    let indexed = refusal(&SIDECAR.replace("requires value <", "requires value[0] <"));
    assert!(
        indexed.contains("so it takes no index; write `value`"),
        "{indexed}"
    );
    let dereferenced = refusal(&SIDECAR.replace("owns value;", "owns *value;"));
    assert!(
        dereferenced.contains("already names what it refers to; write it without `*`"),
        "{dereferenced}"
    );

    // A fact about the referent names it as the sidecar does: the read of
    // the stored referent keeps its name (`docs/internals/raise-lower-principle.md`).
    let false_claim = refusal(&SIDECAR.replace(
        "ensures value == old(value) + 1;",
        "ensures value == old(value) + 2;",
    ));
    assert!(
        false_claim.contains("goal: to_integer(value) == to_integer(old(value)) + 2"),
        "{false_claim}"
    );
    assert!(
        false_claim.contains("resource facts: [owns value, views value]"),
        "{false_claim}"
    );

    // The address of the referent is the pointer the function received, so
    // comparing it with itself holds and adds nothing false.
    let with_address =
        SIDECAR.replace("owns value;", "owns value;\n    requires &value == &value;");
    assert_ne!(with_address, SIDECAR);
    fs::write(&sidecar, &with_address).unwrap();
    let click_project = read_click_project(&sidecar, &with_address).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("the address of a referent is a pointer value");
}

#[test]
fn locked_cpp_artifact_lowers_directly_and_executes_reference_semantics() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let prepared = load_import(&project.config()).expect("load the locked artifact offline");
    let declaration_id = prepared.export().functions[0].declaration_id.clone();
    let function_span = prepared.export().functions[0].span.clone();
    let lowered = lower_import(&prepared).expect("lower the typed artifact directly");

    assert_eq!(lowered.source().identity(), prepared.identity());
    assert_eq!(lowered.source_function().declaration_id, declaration_id);
    assert_eq!(lowered.source_function().span, function_span);
    let function = lowered.kernel_function();
    assert_eq!(function.name(), "increment");
    assert_eq!(function.return_type(), ProgramType::Int32);
    assert_eq!(function.parameters().len(), 1);
    assert_eq!(function.parameters()[0].name(), "value");
    assert_eq!(
        function.parameters()[0].binding_name(),
        &click::kernel::BindingName::reference_carrier("value")
    );
    assert_eq!(
        function.parameters()[0].program_type(),
        ProgramType::Int32Pointer
    );
    assert!(matches!(
        function.body(),
        ProgramStatement::Seq(sequence)
            if { let (store, returned) = (sequence.first(), &sequence.rest()); matches!(
                store.as_ref(),
                ProgramStatement::TypedStore {
                    pointer: ProgramExpression::Variable(pointer),
                    value: ProgramExpression::Add(left, right),
                    value_type: ProgramType::Int32,
                    volatile: false,
                    pointee_constant: false,
                    ..
                } if pointer.reference_referent().is_some_and(|name| name.is_named("value"))
                    && matches!(
                        left.as_ref(),
                        ProgramExpression::TypedLoad {
                            pointer,
                            value_type: ProgramType::Int32,
                            volatile: false,
                            ..
                        } if matches!(pointer.as_ref(), ProgramExpression::Variable(name) if name.reference_referent().is_some_and(|name| name.is_named("value")))
                    )
                    && matches!(right.as_ref(), ProgramExpression::Value(value) if value == &int32(1))
            )
            && matches!(
                returned.as_ref(),
                ProgramStatement::Return(ProgramExpression::TypedLoad {
                    pointer,
                    value_type: ProgramType::Int32,
                    volatile: false,
                    ..
                }) if matches!(pointer.as_ref(), ProgramExpression::Variable(name) if name.reference_referent().is_some_and(|name| name.is_named("value")))
            ) }
    ));

    let pointer = Address {
        base: "cpp-reference".into(),
        offset: AddressOffset::Constant(0),
    };
    let resources =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )));
    let arguments = vec![click::kernel::program_expression::typed_pointer_value(
        pointer.clone(),
        ProgramType::Int32Pointer,
    )];
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().store(pointer.clone(), int32(41)))
        .with_resource_context(resources.clone());
    let expected_state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().store(pointer.clone(), int32(42)))
        .with_resource_context(resources.clone());
    let theorem = prove_symbolic_program_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("the lowered reference function should execute");
    assert_eq!(
        theorem.proposition(),
        &Proposition::ProgramFunctionVerifies {
            state: Box::new(state),
            function: Box::new(function.clone()),
            arguments: arguments.clone(),
            outcome: FunctionOutcome::Return {
                value: int32(42).into(),
                state: Box::new(expected_state),
            },
        }
    );

    let max_state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().store(pointer, int32(i32::MAX as u32)))
        .with_resource_context(resources);
    let overflow = prove_symbolic_program_function_execution(
        max_state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("concrete signed overflow should produce a checked outcome");
    assert_eq!(
        overflow.proposition(),
        &Proposition::ProgramFunctionVerifies {
            state: Box::new(max_state),
            function: Box::new(function.clone()),
            arguments,
            outcome: FunctionOutcome::UndefinedBehavior(UndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn locked_cpp_import_rejects_stale_source_config_and_artifact() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();

    fs::write(project.source(), SOURCE.replace("+ 1", "+ 2")).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("source differs"), "{error}");

    fs::write(project.source(), SOURCE).unwrap();
    project.write_config("other");
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("does not match its description"), "{error}");

    project.write_config("increment");
    let mut artifact = fs::read(project.artifact()).unwrap();
    artifact.push(b' ');
    fs::write(project.artifact(), artifact).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("artifact differs"), "{error}");
}

#[test]
fn cpp_frontend_rejects_unsupported_source_without_a_c_fallback() {
    let project = Project::new();
    fs::write(
        project.source(),
        "int increment(int& value) noexcept {\n    value *= 2;\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("supports only simple assignment"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int increment(volatile int* value) noexcept {\n    return *value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("native element pointer"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct Guard {\n    int& value;\n    explicit Guard(int& input) noexcept : value(input) {}\n    ~Guard() noexcept { value = 0; }\n};\n\nint increment(int& value) noexcept {\n    Guard guard(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("increment.cpp:1"), "{error}");
    assert!(error.contains("record must be standard-layout"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int increment(const int& value) noexcept {\n    value = 7;\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("increment.cpp:2"), "{error}");
    assert!(error.contains("const-qualified"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
// Empty scoped enums still have every value of their fixed backing type.
// Their contracts are integers, while source loads and calls keep nominal IDs.
fn cpp_fixed_byte_enum_forwarding_verifies_and_retains_nominal_identity_offline() {
    let project = Project::with_fixture(
        "enum.cpp",
        "probe",
        "enum class Byte : unsigned char {}; Byte echo(Byte value) noexcept { return value; } Byte probe(Byte value) noexcept { Byte obj = echo(value); return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].return_type,
        CppType::Enumeration {
            is_scoped: true,
            is_fixed: true,
            ..
        }
    ));
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint8 echo(uint8 value) { ensures result == value; } uint8 probe(uint8 value) { ensures result == value; }",
    );
}

#[test]
fn cpp_fixed_byte_enum_explicit_cast_preserves_all_representation_bits_offline() {
    let project = Project::with_fixture(
        "enum.cpp",
        "probe",
        "enum class Byte : unsigned char {}; Byte probe(unsigned int value) noexcept { Byte obj; obj = static_cast<Byte>(value); return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint8 probe(uint32 value) { requires value == 511u32; ensures result == 255u8; }",
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn cpp_fixed_byte_enum_converted_call_results_verify_offline() {
    let project = Project::with_fixture(
        "enum.cpp",
        "probe",
        "enum class Byte : unsigned char {}; unsigned int echo(unsigned int value) noexcept { return value; } Byte probe(unsigned int value) noexcept { return static_cast<Byte>(echo(value)); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint32 echo(uint32 value) { ensures result == value; } uint8 probe(uint32 value) { requires value == 511u32; ensures result == 255u8; }",
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
// Equal backing widths cannot erase distinct enum declarations in a converted
// call result. Only the retained explicit numeric conversion crosses them.
fn cpp_fixed_byte_enum_call_conversions_cannot_erase_nominal_identity() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture(
        "enum.cpp",
        "probe",
        "enum class A : unsigned char {}; enum class B : unsigned char {}; A echo(A value) noexcept { return value; } B probe(A value) noexcept { return static_cast<B>(echo(value)); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint8 echo(uint8 value) { ensures result == value; } uint8 probe(uint8 value) { ensures result == value; }",
    );
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        let cast = &mut forged["functions"][0]["body"][0]["conversions"][0];
        match mutation {
            0 => cast["cast_kind"] = "no_op".into(),
            1 => cast["cast_kind"] = "integral_cast".into(),
            2 => cast["explicit"] = false.into(),
            3 => cast["source_type"]["declaration_id"] = "c:@E@Other".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        assert!(load_import(&project.config()).is_err());
    }
}

#[test]
fn cpp_fixed_byte_enum_artifacts_reject_identity_backing_and_source_forgery() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture(
        "enum.cpp",
        "probe",
        "enum class Byte : unsigned char {}; Byte probe(Byte value) noexcept { return value; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..8 {
        let mut forged = artifact.clone();
        let ty = &mut forged["functions"][0]["body"][0]["value"]["value_type"];
        match mutation {
            0 => ty["declaration_id"] = "c:@E@Other".into(),
            1 => ty["name"] = "Other".into(),
            2 => ty["declaration_id"] = "".into(),
            3 => ty["is_scoped"] = false.into(),
            4 => ty["is_fixed"] = false.into(),
            5 => ty["underlying_type"]["signed"] = true.into(),
            6 => ty["underlying_type"]["bits"] = 32.into(),
            7 => ty["span"]["file"] = "unlocked.hpp".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(
            error.contains("scalar load")
                || error.contains("enum")
                || error.contains("source span")
                || error.contains("return value does not match"),
            "{mutation}: {error}"
        );
    }
}

#[test]
fn cpp_fixed_byte_enum_profile_refuses_other_underlying_and_unscoped_types() {
    for declaration in [
        "enum Byte : unsigned char {};",
        "enum class Byte : signed char {};",
        "enum class Byte : unsigned int {};",
        "enum class Byte {};",
    ] {
        let source = format!("{declaration} Byte probe(Byte value) noexcept {{ return value; }}");
        let project = Project::with_fixture("enum.cpp", "probe", &source);
        assert!(refresh_import(&project.config()).is_err());
        assert!(!project.artifact().exists());
    }
}

#[test]
// Native unsigned-byte forwarding must retain its exact type through a call
// capture, expansion and offline retained verification.
fn cpp_unsigned_byte_call_capture_verifies_offline() {
    let project = Project::with_fixture(
        "bytes.cpp",
        "probe",
        "unsigned char echo(unsigned char value) noexcept { return value; } unsigned char probe(unsigned char value) noexcept { unsigned char obj = echo(value); return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"bytes.cpp\"; uint8 echo(uint8 value) { ensures result == value; } uint8 probe(uint8 value) { ensures result == value; }",
    );
}

#[test]
fn cpp_unsigned_byte_narrowing_preserves_modulo_values_offline() {
    let project = Project::with_fixture(
        "bytes.cpp",
        "probe",
        "unsigned char probe(unsigned int value) noexcept { unsigned char obj; obj = static_cast<unsigned char>(value); return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"bytes.cpp\"; uint8 probe(uint32 value) { requires value == 511u32; ensures result == 255u8; }";
    check_selected_claim_certificate(&project, &import, proof);
    let bad = proof.replace("255u8", "0u8");
    let path = project.directory.join("bad.click");
    fs::write(&path, &bad).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
            .is_err()
    );
}

#[test]
// Clang promotes unsigned bytes to int before multiplying; arithmetic cannot
// accidentally run at byte width and wrap 255 * 255 to one.
fn cpp_unsigned_byte_arithmetic_preserves_integer_promotions_offline() {
    let project = Project::with_fixture(
        "bytes.cpp",
        "probe",
        "unsigned int probe(unsigned char value) noexcept { return value * value; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"bytes.cpp\"; uint32 probe(uint8 value) { requires value == 255u8; ensures result == 65025u32; }",
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
// Adjacent byte fields retain one-byte layout and separate authority; a write
// cannot borrow its neighbor's view or alter the preserved padded word.
fn cpp_unsigned_byte_record_fields_preserve_layout_and_authority_offline() {
    let project = Project::with_fixture(
        "bytes.cpp",
        "probe",
        "struct Bytes { unsigned char first; unsigned char second; unsigned int tail; }; unsigned char probe(Bytes& bytes, unsigned char value) noexcept { bytes.first = value; return bytes.second; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"bytes.cpp\"; uint8 probe(struct Bytes& bytes, uint8 value) { owns bytes.first; views bytes.second; views bytes.tail; ensures bytes.first == value; ensures result == old(bytes.second); ensures bytes.second == old(bytes.second); ensures bytes.tail == old(bytes.tail); }";
    check_selected_claim_certificate(&project, &import, proof);
    let bad = proof.replace("owns bytes.first", "views bytes.first");
    let path = project.directory.join("bad.click");
    fs::write(&path, &bad).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn cpp_unsigned_byte_admission_keeps_other_character_types_outside_profile() {
    for ty in ["signed char", "char", "char8_t", "char16_t"] {
        let source = format!("{ty} probe({ty} value) noexcept {{ return value; }}");
        let project = Project::with_fixture("bytes.cpp", "probe", &source);
        assert!(refresh_import(&project.config()).is_err());
        assert!(!project.artifact().exists());
    }
}

#[test]
// Uninitialized storage has no placeholder value; normal, expanded and retained
// verification must accept a later assignment and refuse an early read.
fn cpp_uninitialized_integer_local_verifies_only_after_assignment_offline() {
    let project = Project::with_fixture(
        "uninitialized.cpp",
        "probe",
        "unsigned int probe(unsigned int value) noexcept { unsigned int obj; obj = value; return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[0],
        CppStatement::Declare {
            initializer: CppInitializer::Uninitialized,
            ..
        }
    ));
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"uninitialized.cpp\"; uint32 probe(uint32 value) { ensures result == value; }",
    );
}

#[test]
fn cpp_uninitialized_integer_read_rejects_even_a_reflexive_claim_offline() {
    let project = Project::with_fixture(
        "uninitialized.cpp",
        "probe",
        "unsigned int probe() noexcept { unsigned int obj; return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = "verifying \"uninitialized.cpp\"; uint32 probe() { ensures result == result; }";
    let path = project.directory.join("bad.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.message().contains("uninitialized"),
        "{}",
        error.message()
    );
}

#[test]
// A rehashed lock cannot use the scalar default-initialization node to erase
// record construction or reference binding.
fn cpp_uninitialized_initializer_rejects_record_and_reference_artifact_forgery() {
    use sha2::{Digest, Sha256};
    for declaration in ["struct Box { int value; };", ""] {
        let local = if declaration.is_empty() {
            "int& obj = value;"
        } else {
            "Box obj{7};"
        };
        let source =
            format!("{declaration} int probe(int& value) noexcept {{ {local} return value; }}");
        let project = Project::with_fixture("uninitialized.cpp", "probe", &source);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let mut artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        artifact["functions"][0]["body"][0]["initializer"] =
            serde_json::json!({"kind":"uninitialized"});
        let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
        let mut lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(
            error.contains("local initializer") || error.contains("record local requires"),
            "{error}"
        );
    }
}

#[test]
fn cpp_scalar_locals_reject_rvalue_reference_and_nested_declarations() {
    let project = Project::scalar_local();
    fs::write(
        project.source(),
        "int relay_value(int& value) noexcept {\n    int&& captured = static_cast<int&&>(value);\n    return captured;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("relay_value.cpp:2"), "{error}");
    assert!(
        error.contains("must resolve to signed/unsigned 32/64/128-bit integer"),
        "{error}"
    );
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int relay_value(bool choose, int& value) noexcept {\n    if (choose) {\n        int captured = value;\n        return captured;\n    }\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("relay_value.cpp:3"), "{error}");
    assert!(
        error.contains("supported only in the function body"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn cpp_direct_calls_reject_missing_throwing_and_recursive_definitions() {
    let project = Project::direct_call();
    fs::write(
        project.source(),
        "int set_seven(int& value);\n\nint call_set_seven(int& value) noexcept {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    // A function defined in another translation unit is exported as its
    // interface (`a_call_into_another_translation_unit_is_checked_against_a_contract`);
    // one that may throw is still refused.
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("call_set_seven.cpp:1"), "{error}");
    assert!(error.contains("must be noexcept"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int set_seven(int& value) {\n    value = 7;\n    return value;\n}\n\nint call_set_seven(int& value) noexcept {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("call_set_seven.cpp:1"), "{error}");
    assert!(error.contains("must declare noexcept"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int call_set_seven(int& value) noexcept {\n    call_set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("recursive C++ calls"), "{error}");
    assert!(
        error.contains("call_set_seven -> call_set_seven"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn cpp_unit_arguments_cannot_leave_the_pinned_slice() {
    // Arguments that override the pinned standard, target or exception mode
    // are Click's to set, and are refused before the export runs.
    for (argument, exceptions) in [
        ("-std=gnu++20", false),
        ("--target=aarch64-unknown-linux-gnu", false),
        ("-fno-exceptions", true),
    ] {
        let project = Project::new();
        let unit = serde_json::json!({
            "language": "c++",
            "exceptions": exceptions,
            "args": ["-funsigned-char", "-ffreestanding", "-nostdinc", "-nostdinc++", argument],
            "sources": {"increment.cpp": {"functions": ["increment"]}},
        });
        let project_file = project.directory.join(click::project::FILE_NAME);
        fs::write(
            &project_file,
            serde_json::to_vec(&serde_json::json!({"units": {"demo": unit}})).unwrap(),
        )
        .unwrap();
        let error = click::project::Project::load(&project_file)
            .and_then(|unit| unit.lock_with_cpp_exporter(Some(&project.exporter)))
            .unwrap_err();
        assert!(
            error.contains(&format!("`{argument}` is set by Click for every C++ unit")),
            "{argument}: {error}"
        );
        assert!(!project.directory.join(click::project::LOCK_NAME).exists());
    }
}

/// Writes a project with one C++ unit exporting `increment` from the
/// fixture's source, with `args` and the project fields `extra`.
fn write_increment_project(project: &Project, args: &[&str], extra: serde_json::Value) -> PathBuf {
    let mut root = serde_json::json!({"units": {"demo": {
        "language": "c++",
        "args": args,
        "sources": {"increment.cpp": {"functions": ["increment"]}},
    }}});
    for (key, value) in extra.as_object().unwrap() {
        root[key] = value.clone();
    }
    let project_file = project.directory.join(click::project::FILE_NAME);
    fs::write(&project_file, serde_json::to_vec(&root).unwrap()).unwrap();
    project_file
}

const INCREMENT_ARGS: &[&str] = &[
    "-funsigned-char",
    "-ffreestanding",
    "-nostdinc",
    "-nostdinc++",
];

/// Copies the regular files under `from` to `to`, keeping relative paths.
#[cfg(not(feature = "fast-gate"))]
fn copy_tree(from: &Path, to: &Path) {
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let target = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            fs::create_dir_all(&target).unwrap();
            copy_tree(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).unwrap();
        }
    }
}

/// A fresh scratch directory for one copy of a project.
#[cfg(not(feature = "fast-gate"))]
fn scratch_copy(name: &str) -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "click-cpp-portable-{name}-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).unwrap();
    directory
}

#[cfg(not(feature = "fast-gate"))]
/// A C++ project lock names the project's own files by their root's label,
/// so it reads the same from every checkout: the committed `basic-cpp` lock
/// verifies from a copy at another path, and preparing the project at two
/// paths writes the same lock and artifacts.
#[test]
#[ignore = "nightly: 4.4s in the parallel gate"]
fn cpp_project_locks_are_portable() {
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/basic-cpp");
    let committed = fs::read_to_string(example.join(click::project::LOCK_NAME)).unwrap();
    assert!(
        !committed.contains("\"/"),
        "the committed lock names an absolute path"
    );
    let copy = scratch_copy("verify");
    copy_tree(&example, &copy);
    for sidecar in [
        "increment.click",
        "with_restore.click",
        "with_restore_caller.click",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_click"))
            .args(["verify", copy.join(sidecar).to_str().unwrap()])
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{sidecar} from a copy: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let exporter = PathBuf::from(
        std::env::var_os("CLICK_CPP_EXPORTER")
            .expect("scripts/check.sh supplies the pinned C++ exporter"),
    );
    let prepared = ["first", "second"].map(|name| {
        let copy = scratch_copy(name);
        copy_tree(&example, &copy);
        click::project::Project::load(&copy.join(click::project::FILE_NAME))
            .and_then(|project| project.lock_with_cpp_exporter(Some(&exporter)))
            .expect("prepare the copy");
        let lock = fs::read_to_string(copy.join(click::project::LOCK_NAME)).unwrap();
        assert!(!lock.contains(copy.to_str().unwrap()), "{lock}");
        let artifact =
            fs::read_to_string(copy.join(".click/captures/basic/increment.cpp.click-cpp.json"))
                .unwrap();
        assert!(!artifact.contains(copy.to_str().unwrap()), "{artifact}");
        let _ = fs::remove_dir_all(&copy);
        (lock, artifact)
    });
    assert_eq!(prepared[0], prepared[1]);
    let _ = fs::remove_dir_all(&copy);
}

#[test]
fn cpp_unit_arguments_follow_the_flag_policy() {
    for (argument, expected) in [
        (
            "-O3",
            "names an optimization level; the project verifies its units at `-O2`",
        ),
        ("-O0", "names an optimization level"),
        ("-fno-strict-aliasing", "is set by Click for every C++ unit"),
        ("-fwrapv", "unsupported C++ argument 5 `-fwrapv`"),
        ("-Xclang", "unsupported C++ argument 5 `-Xclang`"),
        ("-Wl,-z,now", "unsupported C++ argument 5 `-Wl,-z,now`"),
        ("-D__OPTIMIZE__=1", "defines `__OPTIMIZE__`"),
        ("-I", "missing value after argument 5 `-I`"),
    ] {
        let project = Project::new();
        let mut args = INCREMENT_ARGS.to_vec();
        args.push(argument);
        let project_file = write_increment_project(&project, &args, serde_json::json!({}));
        let error = click::project::Project::load(&project_file)
            .and_then(|unit| unit.lock_with_cpp_exporter(Some(&project.exporter)))
            .unwrap_err();
        assert!(error.contains(expected), "{argument}: {error}");
        assert!(!project.directory.join(click::project::LOCK_NAME).exists());
    }
    // Preprocessor inputs and options affecting only code generation or
    // diagnostics are accepted, and the project's level reaches the command.
    let project = Project::new();
    let mut args = INCREMENT_ARGS.to_vec();
    args.extend([
        "-O0",
        "-DNAME=1",
        "-U",
        "OTHER",
        "-I.",
        "-g",
        "-Wall",
        "-Wno-unused-parameter",
        "-fstack-protector-all",
        "-fcf-protection=full",
        "-fstack-clash-protection",
        "-fmacro-prefix-map=a=b",
        "-D_FORTIFY_SOURCE=3",
    ]);
    let project_file =
        write_increment_project(&project, &args, serde_json::json!({"optimization": "-O0"}));
    click::project::Project::load(&project_file)
        .and_then(|unit| unit.lock_with_cpp_exporter(Some(&project.exporter)))
        .expect("accepted arguments lock");
    let lock: serde_json::Value = serde_json::from_slice(
        &fs::read(project.directory.join(click::project::LOCK_NAME)).unwrap(),
    )
    .unwrap();
    let command = &lock["units"]["demo"]["lock"]["c++"]["sources"]["increment.cpp"]["profile"]["compilation_command"];
    assert!(
        command
            .as_array()
            .unwrap()
            .contains(&serde_json::json!("-O0")),
        "{command}"
    );
    assert!(
        !command
            .as_array()
            .unwrap()
            .contains(&serde_json::json!("-fno-strict-aliasing")),
        "{command}"
    );
}

#[test]
fn cpp_optimizer_promises_are_refused_at_an_optimizing_level() {
    for attribute in [
        "__attribute__((nonnull))",
        "__attribute__((returns_nonnull))",
        "__attribute__((const))",
        "__attribute__((pure))",
        "__attribute__((leaf))",
        "__attribute__((returns_twice))",
        "__attribute__((malloc))",
        "__attribute__((assume_aligned(16)))",
        "[[noreturn]]",
        "[[gnu::nonnull]]",
    ] {
        for (optimization, refused) in [("-O2", true), ("-O0", false)] {
            let source = format!(
                "{attribute} int* promised(int* p) noexcept;\n\
                 int* promised(int* p) noexcept {{ return p; }}\n\
                 int increment(int& value) noexcept {{ return *promised(&value); }}\n"
            );
            let project = Project::with_fixture("increment.cpp", "increment", &source);
            let project_file = write_increment_project(
                &project,
                INCREMENT_ARGS,
                serde_json::json!({"optimization": optimization}),
            );
            let result = click::project::Project::load(&project_file)
                .and_then(|unit| unit.lock_with_cpp_exporter(Some(&project.exporter)));
            if refused {
                let error = result.unwrap_err();
                assert!(
                    error.contains("is an optimizer promise Click does not check"),
                    "{attribute}: {error}"
                );
            } else if attribute == "[[noreturn]]" {
                // At `-O0` Clang does not act on it, but warns that this
                // `noreturn` function returns.
                let error = result.unwrap_err();
                assert!(error.contains("should not return"), "{error}");
            } else {
                result.unwrap_or_else(|error| panic!("{attribute} at -O0: {error}"));
            }
        }
    }
}

#[test]
fn exporter_path_is_not_needed_by_offline_load() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    assert!(!Path::new(&project.exporter).exists());
    load_import(&project.config()).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn ordinary_value_methods_import_with_const_receiver_and_mixed_width_fields() {
    let source = include_str!("fixtures/cpp-verification/value-methods/value_methods.cpp");
    for (selected, sidecar_source) in [
        (
            "FeeFrac::IsEmpty",
            include_str!("fixtures/cpp-verification/value-methods/is_empty.click"),
        ),
        (
            "FeeFrac::operator+=",
            include_str!("fixtures/cpp-verification/value-methods/add_disjoint.click"),
        ),
        (
            "double_size",
            include_str!("fixtures/cpp-verification/value-methods/add_self.click"),
        ),
        (
            "double_size_direct",
            include_str!("fixtures/cpp-verification/value-methods/add_self.click"),
        ),
    ] {
        let project = Project::with_fixture("value_methods.cpp", selected, source);
        refresh_import(&project.config()).expect("export the selected value method graph");
        let import = load_import(&project.config()).unwrap();
        assert_eq!(import.export().records[0].fields[0].size_bytes, 8);
        assert_eq!(import.export().records[0].fields[1].size_bytes, 4);
        lower_import(&import).expect("lower the value method graph");
        let sidecar_source = if selected == "double_size_direct" {
            sidecar_source.replace("double_size(", "double_size_direct(")
        } else {
            sidecar_source.to_owned()
        };
        let sidecar = project.directory.join("demo.click");
        fs::write(&sidecar, &sidecar_source).unwrap();
        let parsed = read_click_project(&sidecar, &sidecar_source).unwrap();
        let sites =
            project_smart_tactic_source_sites(&parsed, &ProgramInputs::program(&import)).unwrap();
        let site = sites.first().unwrap();
        let site = project_tactic_source_position(
            &parsed,
            &ProgramInputs::program(&import),
            &site.claim_label,
            site.source_index,
        )
        .unwrap();
        let expanded = expand_project_tactic_source_at(
            &parsed,
            &ProgramInputs::program(&import),
            site.line,
            site.column,
        )
        .unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import)
            .expect("expanded method proof reverifies");
        // Session construction cold-verifies this complete program once.
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        session
            .verify_at_project(&expanded, site.line, site.column)
            .expect("audit session checks the expanded method proof");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn value_methods_reject_false_claims_missing_authority_and_overflow() {
    let source = include_str!("fixtures/cpp-verification/value-methods/value_methods.cpp");
    let add = include_str!("fixtures/cpp-verification/value-methods/add_disjoint.click");
    let empty = include_str!("fixtures/cpp-verification/value-methods/is_empty.click");
    for (selector, proof, expected) in [
        ("FeeFrac::IsEmpty", empty.replace("if old(this->size) == 0", "if old(this->size) == 1"), "unclosed goal"),
        // The receiver is implicit; the retired explicit `this` is refused.
        ("FeeFrac::IsEmpty", empty.replace("bool FeeFrac::IsEmpty() const", "bool FeeFrac_IsEmpty(const struct FeeFrac* this)"), "a C++ member function's `this` is implicit"),
        ("FeeFrac::operator+=", add.replace("ensures this->fee == old(this->fee) + old(other.fee);", "ensures this->fee == old(this->fee);"), "unclosed goal"),
        ("FeeFrac::operator+=", add.replace("    owns this->fee;\n", ""), "missing resource fact"),
        ("FeeFrac::operator+=", add.replace("    requires -4611686018427387904 <= this->fee;\n    requires this->fee <= 4611686018427387903;\n", ""), "overflow"),
        ("FeeFrac::operator+=", add.replace("    requires -1073741824 <= this->size;\n    requires this->size <= 1073741823;\n", ""), "could not establish `-1073741824 <= this->size`"),
    ] {
        let project = Project::with_fixture("value_methods.cpp", selector, source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = project.directory.join("demo.click");
        fs::write(&sidecar, &proof).unwrap();
        let parsed = read_click_project(&sidecar, &proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(error.message().contains(expected), "{selector}: {}", error.message());
    }
}

const SIGNED_ARITHMETIC_SOURCE: &str =
    include_str!("fixtures/cpp-verification/signed-arithmetic/arithmetic.cpp");

/// The C++ spelling of the imported function `declaration_id`, as a sidecar
/// head writes it: `Fee::Evaluate<true>`.
fn cpp_spelling(import: &click::languages::cpp::PreparedCppImport, declaration_id: &str) -> String {
    import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .find(|function| function.declaration_id == declaration_id)
        .expect("an imported function")
        .path
        .join("::")
}

fn check_arithmetic_sidecar(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    check_sidecar_tactic(project, import, source, None);
}

// The paired tool test exercises expansion and retained checking on the same
// complete fixture; its ordinary counterpart needs only direct verification.
fn check_arithmetic_sidecar_with_tools(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
    tools: bool,
) {
    check_sidecar_tactic_with_tools(project, import, source, None, tools);
}

// These semantic regressions already verify the complete original program.
// Spell the selected function's checked certificate directly, then keep the
// independent cold output check and the retained-session check.
fn check_selected_claim_certificate(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    let prefix = format!(
        "{}.",
        click::languages::cpp::names::path_name(&import.export().functions[0].path)
    );
    check_claim_certificate(project, import, source, Some(&prefix));
}

fn check_first_claim_certificate(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    check_claim_certificate(project, import, source, None);
}

fn check_claim_certificate(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
    claim_prefix: Option<&str>,
) {
    let source = source.replace(
        "-9223372036854775808i64",
        "(-9223372036854775807i64 - 1i64)",
    );
    let sidecar = project.directory.join("arithmetic.click");
    fs::write(&sidecar, &source).unwrap();
    let parsed = read_click_project(&sidecar, &source).unwrap();
    let inputs = ProgramInputs::program(import);
    let sites = project_smart_tactic_source_sites(&parsed, &inputs).unwrap();
    let first = match claim_prefix {
        Some(prefix) => sites
            .iter()
            .find(|site| site.claim_label.starts_with(prefix))
            .expect("the selected C++ function has an automated claim"),
        None => sites.first().expect("the sidecar has an automated claim"),
    };
    let claim = &first.claim_label;
    let (session, verified) =
        ProgramVerificationSession::new_program_prepared_project(&parsed, import)
            .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
    assert!(!verified.is_empty());
    let expanded =
        click::surface::expand_verified_function_claim_source_by_label(&source, &verified, claim)
            .expect("the checked selected claim has source spelling")
            .expect("the selected claim is declared in this sidecar");
    let rewritten = parsed.with_entry_source(expanded.clone());
    let position = project_tactic_source_position(&rewritten, &inputs, claim, 0).unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .expect("the written selected claim must verify retained");
    // A cold verification resets the thread-local kernel tables. Finish and
    // drop the retained session first, then check the output independently.
    drop(session);
    verify_program_prepared_project(&rewritten, import)
        .expect("the written selected claim must verify independently");
}

fn check_return_call_sidecar(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    let prefix = format!(
        "{}.",
        click::languages::cpp::names::path_name(&import.export().functions[0].path)
    );
    check_sidecar_tactic(project, import, source, Some(&prefix));
}

fn check_sidecar_tactic(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
    claim_prefix: Option<&str>,
) {
    check_sidecar_tactic_with_tools(project, import, source, claim_prefix, true);
}

fn check_sidecar_tactic_with_tools(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
    claim_prefix: Option<&str>,
    tools: bool,
) {
    let sidecar = project.directory.join("arithmetic.click");
    let source = source.replace(
        "-9223372036854775808i64",
        "(-9223372036854775807i64 - 1i64)",
    );
    fs::write(&sidecar, &source).unwrap();
    let parsed = read_click_project(&sidecar, &source).unwrap();
    verify_program_prepared_project(&parsed, import).unwrap_or_else(|error| {
        panic!(
            "{}\n{}\n{source}",
            error.report(),
            error.trace_context_report().unwrap_or_default()
        )
    });
    if !tools {
        return;
    }
    let sites =
        project_smart_tactic_source_sites(&parsed, &ProgramInputs::program(import)).unwrap();
    let first = match claim_prefix {
        Some(prefix) => sites
            .iter()
            .find(|site| site.claim_label.starts_with(prefix))
            .expect("selected caller tactic"),
        None => sites.first().unwrap(),
    };
    let position = project_tactic_source_position(
        &parsed,
        &ProgramInputs::program(import),
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &parsed,
        &ProgramInputs::program(import),
        position.line,
        position.column,
    )
    .unwrap();
    let rewritten = parsed.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, import).unwrap_or_else(|error| {
        panic!("expanded arithmetic proof: {}\n{expanded}", error.message())
    });
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&parsed, import).unwrap();
    // The expansion may leave the claim no smart tactic; its first written
    // tactic selects it.
    let position = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(import),
        &first.claim_label,
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .expect("retained audit accepts ordinary arithmetic proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn signed_scalar_arithmetic_verifies_through_the_shared_kernel_and_modular_calls() {
    for (selector, source) in [
        (
            "quotient",
            include_str!("fixtures/cpp-verification/signed-arithmetic/quotient.click"),
        ),
        (
            "remainder",
            include_str!("fixtures/cpp-verification/signed-arithmetic/remainder.click"),
        ),
        (
            "multiply",
            include_str!("fixtures/cpp-verification/signed-arithmetic/multiply.click"),
        ),
        (
            "relay",
            include_str!("fixtures/cpp-verification/signed-arithmetic/relay.click"),
        ),
    ] {
        let project = Project::with_fixture("arithmetic.cpp", selector, SIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        lower_import(&import).unwrap();
        check_arithmetic_sidecar(&project, &import, source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn signed_division_correction_covers_rounding_directions_and_boundary_cases() {
    let project =
        Project::with_fixture("arithmetic.cpp", "rounded_divide", SIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    for (n, d, down, result) in [
        (7i64, 3, true, 2i64),
        (7, 3, false, 3),
        (-7, 3, true, -3),
        (-7, 3, false, -2),
        (6, 3, true, 2),
        (6, 3, false, 2),
        (-6, 3, true, -2),
        (-6, 3, false, -2),
        (0, 1, true, 0),
        (0, 1, false, 0),
        (i64::MAX, 1, false, i64::MAX),
        (i64::MIN, 1, true, i64::MIN),
        (i64::MAX, i32::MAX, false, 4294967299),
        (i64::MIN, i32::MAX, true, -4294967299),
    ] {
        let source = format!(
            "verifying \"arithmetic.cpp\";\nint64 rounded_divide(int64 n, int32 d, bool round_down) {{\nrequires n == {n}i64;\nrequires d == {d};\nrequires round_down == {};\nensures result == {result}i64;\n}}\n",
            down
        );
        check_selected_claim_certificate(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn signed_scalar_arithmetic_rejects_undefined_operations_and_false_claims() {
    for (selector, parameters, preconditions, claim, expected) in [
        (
            "quotient",
            "int64 n, int64 d",
            "requires n == 7i64; requires d == 3i64;",
            "result == 3i64",
            "unclosed goal",
        ),
        (
            "rounded_divide",
            "int64 n, int32 d, bool round_down",
            "requires n == -7i64; requires d == 3; requires round_down == true;",
            "result == -2i64",
            "unclosed goal",
        ),
        (
            "quotient",
            "int64 n, int64 d",
            "requires d == 0i64;",
            "result == 0i64",
            "division by zero",
        ),
        (
            "remainder",
            "int64 n, int64 d",
            "requires d == 0i64;",
            "result == 0i64",
            "division by zero",
        ),
        (
            "quotient",
            "int64 n, int64 d",
            "requires n == -9223372036854775808i64; requires d == -1i64;",
            "result == 0i64",
            "overflow",
        ),
        (
            "remainder",
            "int64 n, int64 d",
            "requires n == -9223372036854775808i64; requires d == -1i64;",
            "result == 0i64",
            "overflow",
        ),
        (
            "multiply",
            "int64 a, int64 b",
            "requires a == 2i64;",
            "result == a * b",
            "overflow",
        ),
        (
            "negate",
            "int64 n",
            "requires n == -9223372036854775808i64;",
            "result == 0i64",
            "overflow",
        ),
    ] {
        let project = Project::with_fixture("arithmetic.cpp", selector, SIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arithmetic.cpp\";\nint64 {selector}({parameters}) {{ {preconditions} ensures {claim}; }}\n"
        );
        let source = source.replace(
            "-9223372036854775808i64",
            "(-9223372036854775807i64 - 1i64)",
        );
        fs::write(project.directory.join("arithmetic.click"), &source).unwrap();
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains(expected),
            "{selector}: {}",
            error.message()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn signed_scalar_casts_preserve_cpp20_boolean_and_narrowing_semantics() {
    for (selector, cpp_source, parameters, preconditions, result_type, expected) in [
        (
            "narrow",
            SIGNED_ARITHMETIC_SOURCE,
            "int64 n",
            "requires n == 4294967297i64;",
            "int32",
            "1",
        ),
        (
            "narrow",
            SIGNED_ARITHMETIC_SOURCE,
            "int64 n",
            "requires n == 2147483648i64;",
            "int32",
            "-2147483648",
        ),
        (
            "truth",
            "bool truth(long n) noexcept { return bool(n); }",
            "int64 n",
            "requires n == 4294967296i64;",
            "bool",
            "true",
        ),
        (
            "truth",
            "bool truth(long n) noexcept { return bool(n); }",
            "int64 n",
            "requires n == 0i64;",
            "bool",
            "false",
        ),
        (
            "negate",
            SIGNED_ARITHMETIC_SOURCE,
            "int64 n",
            "requires n == 9223372036854775807i64;",
            "int64",
            "-9223372036854775807i64",
        ),
    ] {
        let project = Project::with_fixture("arithmetic.cpp", selector, cpp_source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arithmetic.cpp\";\n{result_type} {selector}({parameters}) {{ {preconditions} ensures result == {expected}; }}\n"
        );
        check_first_claim_certificate(&project, &import, &source);
    }
    let project = Project::with_fixture(
        "arithmetic.cpp",
        "relay",
        "long quotient(long n, long d) noexcept { return n / d; }\nlong relay(long n, long d, int& untouched) noexcept { int captured = quotient(n, d); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "arithmetic.cpp";
int64 quotient(int64 n, int64 d) {
 requires n == 4294967297i64; requires d == 1i64;
 ensures result == 4294967297i64;
}
int64 relay(int64 n, int64 d, int32& untouched) {
 views untouched;
 requires n == 4294967297i64; requires d == 1i64;
 ensures result == 1i64; ensures untouched == old(untouched);
}
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn subtraction_method_self_aliasing_is_defined_without_bounds_and_frames_caller_memory() {
    let project = Project::with_fixture(
        "subtract_methods.cpp",
        "clear_value",
        include_str!("fixtures/cpp-verification/subtract-methods/subtract_methods.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = include_str!("fixtures/cpp-verification/subtract-methods/clear_value.click");
    check_first_claim_certificate(&project, &import, proof);
    for (source, expected) in [
        (
            proof.replace("ensures this->fee == 0i64", "ensures this->fee == 1i64"),
            "unclosed goal",
        ),
        (
            proof.replace("    owns this->fee;\n", ""),
            "missing resource fact",
        ),
    ] {
        fs::write(project.directory.join("arithmetic.click"), &source).unwrap();
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(error.message().contains(expected), "{}", error.message());
    }
}

#[test]
fn arithmetic_profile_rejects_narrow_and_unsupported_wide_integer_semantics() {
    for source in [
        "__int128 wide(__int128 n) noexcept { return n + 3; }",
        "unsigned short wide(unsigned short n) noexcept { return n / 3; }",
    ] {
        let project = Project::with_fixture("arithmetic.cpp", "wide", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("wide arithmetic supports checked signed multiplication and signed/unsigned division/remainder only")
                || error.contains("signed/unsigned 32/64/128-bit integers"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }
}

#[test]
fn signed_scalar_return_and_parameters_retain_locked_header_aliases() {
    let mut project = Project::with_fixture(
        "arithmetic.cpp",
        "quotient",
        "#include <cstdint>\nint64_t quotient(int64_t n, int64_t d) noexcept { return n / d; }",
    );
    fs::write(
        project.directory.join("cstdint"),
        CONSTEXPR_MAX_MONEY_CSTDINT,
    )
    .unwrap();
    project.dependencies.push("cstdint".into());
    project.write_exception_enabled_compilation_database_with_local_include();
    project.write_config_with_profile("quotient", "arithmetic.cpp", true);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let CppType::Integer { source_aliases, .. } = &import.export().functions[0].return_type else {
        panic!("missing signed return type")
    };
    assert_eq!(source_aliases[0].name, "int64_t");
    assert_eq!(source_aliases[0].span.file, "cstdint");
    check_first_claim_certificate(
        &project,
        &import,
        include_str!("fixtures/cpp-verification/signed-arithmetic/quotient.click"),
    );
}

const UNSIGNED_ARITHMETIC_SOURCE: &str =
    include_str!("fixtures/cpp-verification/unsigned-arithmetic/arithmetic.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn unsigned_scalar_operations_wrap_and_preserve_conversion_semantics() {
    for (name, params, requires, result_type, expected) in [
        ("maximum", "", "", "uint64", "18446744073709551615u64"),
        (
            "mixed",
            "int64 a, uint32 b",
            "requires a == -1i64; requires b == 1u32;",
            "uint64",
            "0u64",
        ),
        (
            "mixed",
            "int64 a, uint32 b",
            "requires a == -1i64; requires b == 1u32;",
            "uint64",
            "0u64",
        ),
        (
            "add64",
            "uint64 a, uint64 b",
            "requires a == 18446744073709551615u64; requires b == 1u64;",
            "uint64",
            "0u64",
        ),
        (
            "sub64",
            "uint64 a, uint64 b",
            "requires a == 0u64; requires b == 1u64;",
            "uint64",
            "18446744073709551615u64",
        ),
        (
            "mul64",
            "uint64 a, uint64 b",
            "requires a == 9223372036854775808u64; requires b == 2u64;",
            "uint64",
            "0u64",
        ),
        (
            "div64",
            "uint64 a, uint64 b",
            "requires a == 18446744073709551615u64; requires b == 2u64;",
            "uint64",
            "9223372036854775807u64",
        ),
        (
            "rem64",
            "uint64 a, uint64 b",
            "requires a == 18446744073709551615u64; requires b == 2u64;",
            "uint64",
            "1u64",
        ),
        (
            "neg64",
            "uint64 a",
            "requires a == 1u64;",
            "uint64",
            "18446744073709551615u64",
        ),
        (
            "add32",
            "uint32 a, uint32 b",
            "requires a == 4294967295u32; requires b == 1u32;",
            "uint32",
            "0u32",
        ),
        (
            "signed_to_unsigned",
            "int32 a",
            "requires a == -1;",
            "uint64",
            "18446744073709551615u64",
        ),
        (
            "narrow_unsigned",
            "int64 a",
            "requires a == -1i64;",
            "uint32",
            "4294967295u32",
        ),
        (
            "narrow_signed",
            "uint64 a",
            "requires a == 18446744073709551615u64;",
            "int32",
            "-1",
        ),
        (
            "widen_unsigned",
            "uint32 a",
            "requires a == 4294967295u32;",
            "int64",
            "4294967295i64",
        ),
        (
            "truth",
            "uint64 a",
            "requires a == 4294967296u64;",
            "bool",
            "true",
        ),
    ] {
        let project = Project::with_fixture("unsigned.cpp", name, UNSIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"unsigned.cpp\";\n{result_type} {name}({params}) {{ {requires} ensures result == {expected}; }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn unsigned_modular_calls_frame_unrelated_memory_and_reject_false_wrap_claims() {
    let project = Project::with_fixture("unsigned.cpp", "relay", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"import click::integer;
verifying "unsigned.cpp";
uint64 add64(uint64 a, uint64 b) { ensures result == integer::uint64_wrapping_add(a, b); }
uint64 relay(uint64 a, uint64 b, int32& untouched) {
 owns untouched;
 ensures result == integer::uint64_wrapping_add(a, b);
 ensures untouched == old(untouched);
}
"#;
    check_first_claim_certificate(&project, &import, source);
    let project = Project::with_fixture("unsigned.cpp", "add64", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "unsigned.cpp";
uint64 add64(uint64 a, uint64 b) {
 requires a == 18446744073709551615u64; requires b == 1u64;
 ensures result == 1u64;
}
"#;
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
fn unsigned_division_rejects_zero() {
    for name in ["div64", "rem64"] {
        let project = Project::with_fixture("unsigned.cpp", name, UNSIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"unsigned.cpp\"; uint64 {name}(uint64 a, uint64 b) {{ requires b == 0u64; ensures result == 0u64; }}"
        );
        fs::write(project.directory.join("bad.click"), &source).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("division by zero"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn compiler_constants_retain_their_origin_and_reject_runtime_calls() {
    let project = Project::with_fixture(
        "constants.cpp",
        "size",
        "unsigned int size() noexcept { return sizeof(unsigned long) + sizeof(unsigned short); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(
        fs::read_to_string(project.artifact())
            .unwrap()
            .contains("compiler_constant")
    );
    check_first_claim_certificate(
        &project,
        &import,
        "verifying \"constants.cpp\"; uint32 size() { ensures result == 10u32; }",
    );
    let project = Project::with_fixture(
        "constants.cpp",
        "size",
        "unsigned long runtime() noexcept; unsigned long size() noexcept { return runtime(); }",
    );
    // A runtime call is not a compiler constant: its callee, defined in
    // another translation unit, is exported as an interface whose contract
    // the sidecar must state.
    refresh_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    assert_eq!(artifact["constants"], serde_json::json!([]), "{artifact}");
    assert_eq!(
        artifact["reachable_functions"][0]["external"], true,
        "{artifact}"
    );
}

#[test]
fn unsigned_positive_divisor_contract_expands_and_reverifies() {
    let project = Project::with_fixture("unsigned.cpp", "div64", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_first_claim_certificate(
        &project,
        &import,
        r#"verifying "unsigned.cpp";
            uint64 div64(uint64 a, uint64 b) {
                requires b > 0u64;
                ensures result == a / b;
            } by {
                have b != 0u64 by {
                    if b == 0u64 {
                        have not (b > 0u64) by {
                            rewrite(b, 0u64);
                            close();
                        }
                        contradiction(b > 0u64);
                    } else {
                        close();
                    }
                }
                step();
                close();
            }
        "#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn unsigned_fee_fast_path_expressions_cover_large_products_and_rounding() {
    // Exact fast-path expressions from EvaluateFee; return the unsigned
    // intermediate; signed-result conversion is covered by signed-conversion fixtures.
    let cpp = include_str!("fixtures/cpp-verification/unsigned-arithmetic/fee_fast_path.cpp");
    for (name, up) in [("down", false), ("up", true)] {
        let project = Project::with_fixture("fast_path.cpp", name, cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        for (fee, at_size, size) in [
            (0i64, 0i32, 1i32),
            (7, 3, 5),
            (8, 3, 6),
            (8589934591, 2147483647, 2147483647),
        ] {
            let numerator = fee as u64 * at_size as u64;
            let expected = if up {
                numerator.div_ceil(size as u64)
            } else {
                numerator / size as u64
            };
            let proof = format!(
                "verifying \"fast_path.cpp\"; uint64 {name}(int64 fee, int32 at_size, int32 size) {{ requires fee == {fee}i64; requires at_size == {at_size}; requires size == {size}; ensures result == {expected}u64; }}"
            );
            check_selected_claim_certificate(&project, &import, &proof);
        }
    }
}

#[test]
fn mixed_unsigned_return_preserves_signed_intermediate_overflow() {
    let project = Project::with_fixture("unsigned.cpp", "mixed", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = "verifying \"unsigned.cpp\"; uint64 mixed(int64 a, uint32 b) { requires a == 9223372036854775807i64; requires b == 4294967295u32; ensures result == 0u64; }";
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn compiler_constant_calls_preserve_runtime_constant_evaluation_context() {
    // A constexpr function can distinguish constant evaluation from a runtime
    // call. The exporter must fold the latter meaning in an imported body.
    let cpp = "namespace std { template<class T> struct numeric_limits { static constexpr unsigned long max() noexcept { return __builtin_is_constant_evaluated() ? 1UL : 2UL; } }; } unsigned long probe() noexcept { return std::numeric_limits<unsigned long>::max(); }";
    let project = Project::with_fixture("constant_context.cpp", "probe", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_first_claim_certificate(
        &project,
        &import,
        "verifying \"constant_context.cpp\"; uint64 probe() { ensures result == 2u64; }",
    );
    let bad = "verifying \"constant_context.cpp\"; uint64 probe() { ensures result == 1u64; }";
    fs::write(project.directory.join("bad.click"), bad).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), bad).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

const TEMPLATE_INSTANCE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/template-instances/instances.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn concrete_template_instances_have_distinct_identities_and_modular_contracts() {
    let project = Project::with_fixture("instances.cpp", "both", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let helpers = &import.export().reachable_functions;
    assert_eq!(helpers.len(), 2);
    assert_ne!(helpers[0].declaration_id, helpers[1].declaration_id);
    assert_eq!(helpers[0].name, "choose__bool_true");
    assert_eq!(helpers[1].name, "choose__bool_false");
    for (helper, chosen_then) in [(&helpers[0], true), (&helpers[1], false)] {
        let CppStatement::If {
            condition,
            then_branch,
            else_branch,
            span,
        } = &helper.body[0]
        else {
            panic!("constexpr selection must retain its conditional span");
        };
        assert_eq!(span.file, "instances.cpp");
        assert_eq!(span.start_line, 4);
        assert_eq!(then_branch.is_empty(), !chosen_then);
        assert_eq!(else_branch.is_empty(), chosen_then);
        let click::languages::cpp::CppCondition::Expression(CppExpression::IntegralCast {
            value,
            ..
        }) = condition
        else {
            panic!("typed Boolean selection")
        };
        assert!(matches!(
            value.as_ref(),
            CppExpression::CompilerConstant { .. }
        ));
    }
    let sidecar = r#"verifying "instances.cpp";
int32 choose<true>(int32 a, int32 b) {
 requires a >= -1073741824; requires a <= 1073741823;
 ensures result == a; ensures result >= -1073741824; ensures result <= 1073741823;
}
int32 choose<false>(int32 a, int32 b) {
 requires b >= -1073741824; requires b <= 1073741823;
 ensures result == b; ensures result >= -1073741824; ensures result <= 1073741823;
}
int32 both(int32 a, int32 b, int32* untouched) {
 requires a >= -1073741824; requires a <= 1073741823;
 requires b >= -1073741824; requires b <= 1073741823;
 owns untouched[0..1];
 ensures result == a + b;
 ensures untouched[0] == old(untouched[0]);
}
"#;
    check_first_claim_certificate(&project, &import, sidecar);
    let hostile = sidecar.replace("ensures result == b;", "ensures result == a;");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn concrete_scalar_type_template_instances_preserve_width_and_signedness() {
    let project = Project::with_fixture("instances.cpp", "widths", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().reachable_functions[0].name, "identity__int");
    assert_eq!(
        import.export().reachable_functions[1].name,
        "identity__unsigned_long"
    );
    let sidecar = r#"verifying "instances.cpp";
int32 identity<int>(int32 value) { ensures result == value; }
uint64 identity<unsigned long>(uint64 value) { ensures result == value; }
uint64 widths(int32 a, uint64 b) {
 requires a == 1; requires b == 18446744073709551615u64;
 ensures result == 0u64;
}
"#;
    check_first_claim_certificate(&project, &import, sidecar);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn concrete_member_template_instances_preserve_receiver_authority() {
    let project = Project::with_fixture("instances.cpp", "member", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "instances.cpp";
int64 Value::select<true>() const {
 views this->fee;
 ensures result == this->fee;
 ensures this->fee == old(this->fee);
}
int64 Value::select<false>() const {
 views this->fee;
 ensures result == 0i64;
 ensures this->fee == old(this->fee);
}
int64 member(const struct Value& value) {
 owns value.fee;
 ensures result == value.fee;
 ensures value.fee == old(value.fee);
}
"#;
    check_first_claim_certificate(&project, &import, sidecar);
    let hostile = sidecar.replace(" owns value.fee;", "");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn constexpr_discards_only_the_compiler_selected_arm() {
    let project = Project::with_fixture("instances.cpp", "accepted", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().reachable_functions.len(), 1);
    let sidecar = r#"verifying "instances.cpp";
int32 bounded<true>(int32 value) { ensures result == value; }
int32 accepted(int32 value) { ensures result == value; }
"#;
    check_first_claim_certificate(&project, &import, sidecar);
    let rejected = Project::with_fixture("instances.cpp", "rejected", TEMPLATE_INSTANCE_SOURCE);
    // The selected arm calls `unavailable`, declared without a parameter
    // name and defined in no translation unit here.
    let error = refresh_import(&rejected.config()).unwrap_err();
    assert!(
        error.contains("`unavailable` must name every parameter"),
        "{error}"
    );
    assert!(!rejected.artifact().exists());
}

#[test]
fn template_type_identity_does_not_merge_equal_width_cpp_types() {
    let project = Project::with_fixture("instances.cpp", "exact_types", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let helpers = &import.export().reachable_functions;
    assert_eq!(helpers[0].name, "identity__unsigned_long");
    assert_eq!(helpers[1].name, "identity__unsigned_long_long");
    assert_ne!(helpers[0].declaration_id, helpers[1].declaration_id);
    let source = r#"import click::integer;
verifying "instances.cpp";
uint64 identity<unsigned long>(uint64 value) { ensures result == value; }
uint64 identity<unsigned long long>(uint64 value) { ensures result == value; }
uint64 exact_types(uint64 a, uint64 b) { ensures result == integer::uint64_wrapping_add(a, b); }
"#;
    check_first_claim_certificate(&project, &import, source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn constexpr_conditions_use_constant_context_and_allow_absent_else() {
    for (selected, params, expected) in [
        ("constant_context", "", "1"),
        ("discarded_without_else", "int32 value", "value"),
    ] {
        let project = Project::with_fixture("instances.cpp", selected, TEMPLATE_INSTANCE_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert!(import.export().reachable_functions.is_empty());
        let source = format!(
            "verifying \"instances.cpp\"; int32 {selected}({params}) {{ ensures result == {expected}; }}"
        );
        check_first_claim_certificate(&project, &import, &source);
    }
    let project = Project::with_fixture("instances.cpp", "runtime_if", TEMPLATE_INSTANCE_SOURCE);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("must name every parameter in its declaration"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn substituted_boolean_template_arguments_are_typed_values() {
    let project = Project::with_fixture("instances.cpp", "get_flag", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "instances.cpp";
int32 flag<true>() { ensures result == 1; }
int32 get_flag() { ensures result == 1; }
"#;
    check_first_claim_certificate(&project, &import, source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn integral_template_values_preserve_exact_type_sign_and_full_width() {
    let project = Project::with_fixture(
        "values.cpp",
        "call",
        "template<auto N> int identity(int value) noexcept { return value; }\n\
         int call(int value) noexcept {\n\
             int a = identity<-1>(value);\n\
             int b = identity<1U>(a);\n\
             int c = identity<0UL>(b);\n\
             int d = identity<18446744073709551615UL>(c);\n\
             return identity<18446744073709551615ULL>(d);\n\
         }\n",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let helpers = &import.export().reachable_functions;
    let names = [
        "identity__value_int_neg_1",
        "identity__value_unsigned_int_1",
        "identity__value_unsigned_long_0",
        "identity__value_unsigned_long_18446744073709551615",
        "identity__value_unsigned_long_long_18446744073709551615",
    ];
    assert_eq!(helpers.len(), names.len());
    let mut identities = std::collections::BTreeSet::new();
    let mut sidecar = "verifying \"values.cpp\";\n".to_string();
    for (helper, name) in helpers.iter().zip(names) {
        assert_eq!(helper.name, name);
        assert!(identities.insert(&helper.declaration_id));
        // Clang prints each value with its type's suffix, `identity<1U>`; the
        // sidecar names the instance as the importer does.
        let name = click::languages::cpp::names::path_name(&helper.path);
        sidecar.push_str(&format!(
            "int32 {name}(int32 value) {{ ensures result == value; }}\n"
        ));
    }
    sidecar.push_str("int32 call(int32 value) { ensures result == value; }");
    check_first_claim_certificate(&project, &import, &sidecar);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn integral_class_extents_and_unsigned_fields_use_native_typed_cells() {
    let project = Project::with_fixture(
        "extent.cpp",
        "size",
        "template<unsigned long N> struct Extent { unsigned long length; unsigned int marker; ~Extent() = default; };\n\
         unsigned long size(Extent<18446744073709551615UL>& span) noexcept {\n\
             span.marker = 4294967295U;\n\
             return span.length;\n\
         }\n",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(
        import.export().records[0].name,
        "Extent__value_unsigned_long_18446744073709551615"
    );
    let sidecar = r#"verifying "extent.cpp";
uint64 size(struct Extent__value_unsigned_long_18446744073709551615& span) {
 owns span.length; owns span.marker;
 requires span.length == 18446744073709551615u64;
 ensures result == 18446744073709551615u64;
 ensures span.length == old(span.length);
 ensures span.marker == 4294967295u32;
}
"#;
    check_first_claim_certificate(&project, &import, sidecar);
    for denied in [" owns span.length;", " owns span.marker;"] {
        let hostile = sidecar.replace(denied, "");
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn explicitly_defaulted_trivial_destructor_uses_ordinary_local_lifetime() {
    let project = Project::with_fixture(
        "defaulted.cpp",
        "read",
        "struct Value { int value; ~Value() = default; };\n\
         int read(int input) noexcept { Value local{input}; return local.value; }\n",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(import.export().records[0].destructor.is_none());
    check_first_claim_certificate(
        &project,
        &import,
        "verifying \"defaulted.cpp\"; int32 read(int32 input) { ensures result == input; }",
    );
}

#[test]
fn deleted_destructors_do_not_enter_the_defaulted_trivial_profile() {
    let project = Project::with_fixture(
        "deleted.cpp",
        "read",
        "struct Value { int value; ~Value() = delete; };\n\
         int read(const Value& input) noexcept { return input.value; }\n",
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains(
            "destructor must be public, non-virtual outside a polymorphic class, non-deleted"
        ),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn unsupported_template_arguments_and_dependent_selection_fail_explicitly() {
    for (selected, source, diagnostic) in [
        (
            "call",
            "template<short N> int f(int value) noexcept { return value; } int call(int value) noexcept { int result = f<1>(value); return result; }",
            "integral template arguments require",
        ),
        (
            "call",
            "template<class T> int f(int value) noexcept { return value; } int call(int value) noexcept { int result = f<int*>(value); return result; }",
            "template type arguments require",
        ),
        (
            "call",
            "template<class... T> int f(int value) noexcept { return value; } int call(int value) noexcept { int result = f<int>(value); return result; }",
            "template arguments require Boolean",
        ),
        (
            "f",
            "template<bool B> int f(int value) noexcept { return value; }",
            "dependent template pattern",
        ),
    ] {
        let project = Project::with_fixture("unsupported.cpp", selected, source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn instantiated_fee_fast_paths_preserve_both_rounding_expressions() {
    for (fee, at_size, size) in [
        (0u64, 1u64, 3u64),
        (7, 2, 3),
        (8, 2, 4),
        (8589934591, 2147483647, 2147483647),
    ] {
        for (selected, instance, expected) in [
            ("fee_down", "fee_fast_path<true>", fee * at_size / size),
            (
                "fee_up",
                "fee_fast_path<false>",
                (fee * at_size).div_ceil(size),
            ),
        ] {
            let project =
                Project::with_fixture("instances.cpp", selected, TEMPLATE_INSTANCE_SOURCE);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let contract = format!(
                "requires fee == {fee}i64; requires at_size == {at_size}; requires size == {size}; ensures result == {expected}u64;"
            );
            let source = format!(
                "verifying \"instances.cpp\"; uint64 {instance}(int64 fee, int32 at_size, int32 size) {{ {contract} }} uint64 {selected}(int64 fee, int32 at_size, int32 size) {{ {contract} }}"
            );
            check_selected_claim_certificate(&project, &import, &source);
            let hostile = source.replace(
                &format!("result == {expected}u64"),
                &format!("result == {}u64", expected + 1),
            );
            fs::write(project.directory.join("bad.click"), &hostile).unwrap();
            let parsed =
                read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

const CLASS_INSTANCE_SOURCE: &str = r#"
struct SizeTag {};
struct WeightTag {};
template<class T, bool Flag = false> struct Box {
    int value;
    int Read() const noexcept { return value; }
};
using Integer = int;
int call(const Box<Integer>& box) noexcept { return box.Read(); }
int wide(const Box<long long>& box) noexcept { return box.Read(); }
int long_type(const Box<long>& box) noexcept { return box.Read(); }
int plain(const Box<int>& box) noexcept { return box.Read(); }
int tagged(const Box<SizeTag, true>& box) noexcept { return box.Read(); }
int other_tag(const Box<WeightTag, true>& box) noexcept { return box.Read(); }
int both(const Box<SizeTag, true>& left, const Box<WeightTag, true>& right) noexcept { return left.Read(); }
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn class_template_instances_preserve_nominal_identity_and_verify_offline() {
    let mut alias_identity = None;
    let mut identities = std::collections::BTreeSet::new();
    for (selected, record, spelling) in [
        ("call", "Box__int__bool_false", "Box<int>"),
        ("wide", "Box__long_long__bool_false", "Box<long long>"),
        ("long_type", "Box__long__bool_false", "Box<long>"),
        (
            "tagged",
            "Box__tag_SizeTag__bool_true",
            "Box<SizeTag, true>",
        ),
        (
            "other_tag",
            "Box__tag_WeightTag__bool_true",
            "Box<WeightTag, true>",
        ),
    ] {
        let project = Project::with_fixture("instances.cpp", selected, CLASS_INSTANCE_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert_eq!(import.export().records.len(), 1);
        let instance = &import.export().records[0];
        assert_eq!(instance.name, record);
        assert!(identities.insert(instance.declaration_id.clone()));
        if selected == "call" {
            alias_identity = Some(instance.declaration_id.clone());
        }
        assert_eq!(instance.size_bytes, 4);
        assert_eq!(instance.fields[0].name, "value");
        assert_eq!(
            import.export().reachable_functions[0].name,
            format!("{record}_Read")
        );
        // The member and the record type are written as C++ names them, by
        // the instance Clang prints, a defaulted argument left out.
        assert_eq!(instance.path, [spelling]);
        let sidecar = format!(
            "verifying \"instances.cpp\"; int32 {spelling}::Read() const {{ views this->value; ensures result == this->value; }} int32 {selected}(const {spelling}& box) {{ views box.value; ensures result == box.value; }}"
        );
        fs::remove_file(&project.exporter).unwrap();
        check_selected_claim_certificate(
            &project,
            &load_import(&project.config()).unwrap(),
            &sidecar,
        );
    }
    let plain = Project::with_fixture("instances.cpp", "plain", CLASS_INSTANCE_SOURCE);
    refresh_import(&plain.config()).unwrap();
    assert_eq!(
        load_import(&plain.config()).unwrap().export().records[0].declaration_id,
        alias_identity.unwrap()
    );
}

// A class template named with its parameters, `Cell<T>`, is exported at an
// abstract type argument, which a body may only copy, and each instance's
// methods have that body. A body that could mean something else at another
// type, or a specialization that is another body, is refused at export.
#[test]
fn generic_class_templates_refuse_bodies_that_differ_by_type() {
    let cell = |body: &str, extra: &str| {
        format!(
            "template<class T> class Cell {{ T value; public: void set(T v) noexcept {{ value = v; {body} }} }}; {extra} void store(Cell<int>& cell, int x) noexcept {{ cell.set(x); }}"
        )
    };
    for (source, templates, diagnostic) in [
        (
            cell("unsigned long size = sizeof(T);", ""),
            "Cell<T>",
            "a size or alignment of a template argument",
        ),
        (
            cell("if constexpr (sizeof(T) == 4) { value = v; }", ""),
            "Cell<T>",
            "an `if constexpr`",
        ),
        (
            cell("keep(v);", "").replacen(
                "template<class T> class Cell",
                "template<class U> void keep(U) noexcept {} template<class T> class Cell",
                1,
            ),
            "Cell<T>",
            "passed only to the template's own methods",
        ),
        (
            cell(
                "",
                "template<> class Cell<long> { long value; public: void set(long v) noexcept { value = v; } };",
            ),
            "Cell<T>",
            "may not be specialized",
        ),
        (
            cell(
                "",
                "template<> void Cell<int>::set(int v) noexcept { value = v; }",
            ),
            "Cell<T>",
            "not a specialization",
        ),
        (cell("", ""), "Missing<T>", "was not found"),
        (
            cell("", ""),
            "Cell<T, U>",
            "takes the type parameters its options name",
        ),
    ] {
        let project = Project::with_fixture("cell.cpp", "store", &source);
        project.write_config_with_templates("store", &[templates]);
        let error = refresh_import(&project.config())
            .err()
            .unwrap_or_else(|| panic!("{source} exported"));
        assert!(error.contains(diagnostic), "{source}: {error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn class_template_instances_use_resolved_storage_types_and_constructor_names() {
    let source = r#"
        template<class T> struct Stored {
            T value;
            explicit Stored(T next) noexcept : value(next) {}
            T Read() const noexcept { return value; }
            ~Stored() noexcept { value = 0; }
        };
        long long create(long long next) noexcept {
            Stored<long long> box(next);
            return box.Read();
        }
    "#;
    let ordinary = source
        .replace("template<class T> struct Stored", "struct Stored")
        .replace("T value", "long long value")
        .replace("T next", "long long next")
        .replace("T Read", "long long Read")
        .replace("Stored<long long>", "Stored");
    for (cpp, record) in [(source, "Stored__long_long"), (ordinary.as_str(), "Stored")] {
        let project = Project::with_fixture("stored.cpp", "create", cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert_eq!(import.export().records[0].fields[0].size_bytes, 8);
        let sidecar = r#"
        verifying "stored.cpp";
        Stored<long long>::Stored(int64 next) {
            owns this->value; ensures this->value == next;
        }
        int64 Stored<long long>::Read() const {
            views this->value; ensures result == this->value;
        }
        Stored<long long>::~Stored() {
            owns this->value; ensures this->value == 0i64;
        }
        int64 create(int64 next) {
            ensures result == next;
        }
    "#;
        // A class template instance's members are written as C++ writes
        // them, as an ordinary class's are.
        let ordinary_sidecar = r#"
        verifying "stored.cpp";
        Stored::Stored(int64 next) {
            owns this->value; ensures this->value == next;
        }
        int64 Stored::Read() const {
            views this->value; ensures result == this->value;
        }
        Stored::~Stored() {
            owns this->value; ensures this->value == 0i64;
        }
        int64 create(int64 next) {
            ensures result == next;
        }
    "#;
        fs::remove_file(&project.exporter).unwrap();
        check_selected_claim_certificate(
            &project,
            &import,
            if record == "Stored" {
                ordinary_sidecar
            } else {
                sidecar
            },
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn class_template_instances_reject_cross_instance_bindings_even_with_equal_layouts() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture("instances.cpp", "both", CLASS_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let records = &import.export().records;
    assert_eq!(records.len(), 2);
    assert_ne!(records[0].declaration_id, records[1].declaration_id);
    assert_ne!(
        records[0].fields[0].declaration_id,
        records[1].fields[0].declaration_id
    );
    assert_eq!(records[0].size_bytes, records[1].size_bytes);
    let sidecar = r#"
        verifying "instances.cpp";
        int32 Box<SizeTag, true>::Read() const {
            views this->value; ensures result == this->value;
        }
        int32 both(const Box<SizeTag, true>& left,
                   const struct Box__tag_WeightTag__bool_true& right) {
            views left.value; views right.value;
            ensures result == left.value;
            ensures right.value == old(right.value);
        }
    "#;
    fs::remove_file(&project.exporter).unwrap();
    check_selected_claim_certificate(&project, &import, sidecar);
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let right = artifact["functions"][0]["parameters"][1].clone();
    let place = &mut artifact["functions"][0]["body"][0]["arguments"][0]["place"];
    place["declaration_id"] = right["declaration_id"].clone();
    place["name"] = right["name"].clone();
    let bytes = serde_json::to_vec(&artifact).unwrap();
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    lock_source_mut(&mut lock)["artifact"]["sha256"] =
        format!("{:x}", Sha256::digest(&bytes)).into();
    lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
    fs::write(project.artifact(), bytes).unwrap();
    fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("unsupported argument"), "{error}");
}

#[test]
fn class_template_instances_complete_unused_parameter_types_without_source_edits() {
    let source = "template<class T> struct Box { T value; }; int call(const Box<int>& box) noexcept { return 7; }";
    let project = Project::with_fixture("unused.cpp", "call", source);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().records[0].name, "Box__int");
    assert_eq!(import.export().records[0].fields[0].size_bytes, 4);
    fs::remove_file(&project.exporter).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"
        verifying "unused.cpp";
        int32 call(const Box<int>& box) { ensures result == 7; }
    "#,
    );
}

#[test]
fn class_template_instances_retain_argument_and_layout_boundaries() {
    for (source, diagnostic) in [
        (
            "enum class Other : unsigned char {}; template<class T> struct Box { int value; }; int call(const Box<Other>& box) noexcept { return box.value; }",
            "named empty trivial tags",
        ),
        (
            "namespace std { enum class byte : unsigned char {}; } template<class T> struct Box { int value; }; int call(const Box<std::byte>& box) noexcept { return box.value; }",
            "std::byte requires the pinned standard declaration span",
        ),
        (
            "template<short N> struct Box { int value; }; int call(const Box<1>& box) noexcept { return box.value; }",
            "integral template arguments require",
        ),
        (
            "template<class T> struct Box { int value; }; int call(const Box<volatile int>& box) noexcept { return box.value; }",
            "qualified C++ template type arguments",
        ),
        (
            "struct Tag { int value; }; template<class T> struct Box { int value; }; int call(const Box<Tag>& box) noexcept { return box.value; }",
            "named empty trivial tags",
        ),
        (
            "template<class T> struct Box { int value; }; int call(const Box<int*>& box) noexcept { return box.value; }",
            "named empty trivial tags",
        ),
        (
            "template<class... T> struct Box { int value; }; int call(const Box<int>& box) noexcept { return box.value; }",
            "C++ template arguments require Boolean",
        ),
        (
            "namespace A_B { struct Tag {}; } namespace A { struct B_Tag {}; } template<class T> struct Box { int value; }; int call(const Box<A_B::Tag>& a, const Box<A::B_Tag>& b) noexcept { return a.value; }",
            "same-named record layouts",
        ),
    ] {
        let project = Project::with_fixture("unsupported.cpp", "call", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

const BASE_LAYOUT_SOURCE: &str = r#"
struct Base { long long fee; int size; };
struct SizeTag {}; struct WeightTag {};
template<class Tag> struct Rate : public Base {};
struct Envelope { Rate<SizeTag> left; Rate<WeightTag> right; int untouched; };
int read(const Envelope& state) noexcept { return state.untouched; }
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn single_base_layouts_preserve_nominal_subobjects_and_verify_offline() {
    let project = Project::with_fixture("bases.cpp", "read", BASE_LAYOUT_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().records.len(), 4);
    let base = import
        .export()
        .records
        .iter()
        .find(|record| record.name == "Base")
        .unwrap();
    let mut identities = std::collections::BTreeSet::new();
    for record in import
        .export()
        .records
        .iter()
        .filter(|record| record.base.is_some())
    {
        assert!(record.fields.is_empty());
        assert!(identities.insert(record.declaration_id.clone()));
        let subobject = record.base.as_ref().unwrap();
        assert_eq!(
            subobject.value_type,
            CppType::Record {
                declaration_id: base.declaration_id.clone(),
                name: "Base".into(),
                is_const: false,
            }
        );
        assert_eq!(subobject.offset_bytes, 0);
        assert_eq!(subobject.size_bytes, base.size_bytes);
    }
    assert_eq!(identities.len(), 2);
    fs::remove_file(&project.exporter).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"
        verifying "bases.cpp";
        int32 read(const struct Envelope& state) {
            views state.left.base.fee; views state.right.base.size;
            views state.untouched;
            ensures result == state.untouched;
            ensures state.left.base.fee == old(state.left.base.fee);
            ensures state.right.base.size == old(state.right.base.size);
        }
    "#,
    );
}

#[test]
fn single_base_layouts_reject_forged_edges_layouts_and_flattened_fields() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture("bases.cpp", "read", BASE_LAYOUT_SOURCE);
    refresh_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let original_lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    let index = artifact["records"]
        .as_array()
        .unwrap()
        .iter()
        .position(|record| record.get("base").is_some())
        .unwrap();
    for mutation in 0..8 {
        let mut hostile = artifact.clone();
        let record = &mut hostile["records"][index];
        match mutation {
            0 => record["base"]["value_type"]["declaration_id"] = "unknown".into(),
            1 => record["base"]["value_type"]["name"] = "Other".into(),
            2 => record["base"]["offset_bytes"] = 4.into(),
            3 => record["base"]["size_bytes"] = 8.into(),
            4 => record["size_bytes"] = 32.into(),
            5 => record["base"]["value_type"]["is_const"] = true.into(),
            6 => {
                record["base"]["value_type"]["declaration_id"] = record["declaration_id"].clone();
                record["base"]["value_type"]["name"] = record["name"].clone();
            }
            7 => {
                let fields = artifact["records"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|item| item["name"] == "Base")
                    .unwrap()["fields"]
                    .clone();
                record["fields"] = fields;
                record.as_object_mut().unwrap().remove("base");
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&hostile).unwrap();
        let mut lock = original_lock.clone();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "accepted base mutation {mutation}"
        );
    }
}

#[test]
fn single_base_layouts_retain_source_and_execution_boundaries() {
    for (declaration, diagnostic) in [
        ("struct Rate : private Base {};", "public non-virtual"),
        ("struct Rate : virtual Base {};", "public non-virtual"),
        (
            "struct Other { int value; }; struct Rate : Base, Other {};",
            "one public non-virtual base",
        ),
        ("struct Rate : Base { int extra; };", "no own fields"),
        (
            "struct Empty {}; struct Rate : Empty {};",
            "at least one field",
        ),
        (
            "struct Rate : Base { ~Rate() noexcept { } };",
            "trivial copying/destruction",
        ),
    ] {
        let source = format!(
            "struct Base {{ int value; }}; {declaration} int read(const Rate& state) noexcept {{ return 7; }}"
        );
        let project = Project::with_fixture("unsupported_base.cpp", "read", &source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
    let source = "struct Base { int value; }; struct Rate : Base {}; int read(const Rate& state) noexcept { return static_cast<const Base&>(state).value; }";
    let project = Project::with_fixture("inherited.cpp", "read", source);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("can access only current function"),
        "{error}"
    );
    assert!(!project.artifact().exists());
    let source = "struct Base { int value; }; struct Rate : Base { explicit Rate(int next) noexcept : Base{next} {} }; int read(int next) noexcept { Rate state(next); return 7; }";
    let project = Project::with_fixture("constructed_base.cpp", "read", source);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("constructors with base subobjects"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

const INHERITED_SOURCE: &str = r#"
struct Base;
struct Deep;
struct Base {
    long long fee; int size;
    int Read() const noexcept { return size; }
    void Set(int next) noexcept { size = next; }
};
struct Other { long long fee; int size; };
struct SizeTag {}; struct WeightTag {};
template<class Tag> struct Rate : Base {};
struct Deep : Rate<SizeTag> {
    int Observe() const noexcept { return size; }
};
struct Envelope {
    Deep left; Rate<WeightTag> right; Other unrelated;
    int Read() const noexcept { return left.size; }
    int Via() const noexcept { return left.Read(); }
    void Write(int next) noexcept { right.Set(next); }
    void Copy() noexcept { right.size = left.size; }
};
int read(const Deep& state) noexcept { return state.size; }
long long fee(const Deep& state) noexcept { return state.fee; }
int Helper(const Base& value) noexcept { return value.size; }
void SetHelper(Base& value, int next) noexcept { value.size = next; }
int call(const Envelope& state) noexcept { return Helper(state.left); }
void change(Envelope& state, int next) noexcept { SetHelper(state.right, next); }
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn inherited_field_paths_preserve_base_authority_and_verify_offline() {
    for (selected, contract) in [
        (
            "read",
            "int32 read(const struct Deep& state) { views state.base.base.size; ensures result == state.base.base.size; }",
        ),
        (
            "fee",
            "int64 fee(const struct Deep& state) { views state.base.base.fee; ensures result == state.base.base.fee; }",
        ),
        (
            "Deep::Observe",
            "int32 Deep::Observe() const { views this->base.base.size; ensures result == this->base.base.size; }",
        ),
        (
            "Envelope::Read",
            "int32 Envelope::Read() const { views this->left.base.base.size; ensures result == this->left.base.base.size; }",
        ),
        (
            "Envelope::Copy",
            "void Envelope::Copy() { views this->left.base.base.size; owns this->right.base.size; ensures this->right.base.size == this->left.base.base.size; ensures this->left.base.base.size == old(this->left.base.base.size); }",
        ),
    ] {
        let project = Project::with_fixture("inherited.cpp", selected, INHERITED_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = format!("verifying \"inherited.cpp\"; {contract}");
        fs::remove_file(&project.exporter).unwrap();
        check_selected_claim_certificate(&project, &import, &sidecar);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn inherited_method_and_reference_calls_verify_offline_with_sibling_frames() {
    for (selected, sidecar) in [
        (
            "Envelope::Via",
            r#"
        int32 Base::Read() const { views this->size; ensures result == this->size; }
        int32 Envelope::Via() const { views this->left.base.base.size; views this->right.base.size; ensures result == this->left.base.base.size; ensures this->right.base.size == old(this->right.base.size); }
        "#,
        ),
        (
            "Envelope::Write",
            r#"
        void Base::Set(int32 next) { owns this->size; ensures this->size == next; }
        void Envelope::Write(int32 next) { owns this->right.base.size; views this->left.base.base.size; ensures this->right.base.size == next; ensures this->left.base.base.size == old(this->left.base.base.size); }
        "#,
        ),
        (
            "call",
            r#"
        int32 Helper(const struct Base& value) { views value.size; ensures result == value.size; }
        int32 call(const struct Envelope& state) { views state.left.base.base.size; views state.unrelated.size; ensures result == state.left.base.base.size; ensures state.unrelated.size == old(state.unrelated.size); }
        "#,
        ),
        (
            "change",
            r#"
        void SetHelper(struct Base& value, int32 next) { owns value.size; ensures value.size == next; }
        void change(struct Envelope& state, int32 next) { owns state.right.base.size; views state.left.base.base.size; ensures state.right.base.size == next; ensures state.left.base.base.size == old(state.left.base.base.size); }
        "#,
        ),
    ] {
        let project = Project::with_fixture("inherited.cpp", selected, INHERITED_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        check_selected_claim_certificate(
            &project,
            &import,
            &format!("verifying \"inherited.cpp\"; {sidecar}"),
        );
    }
}

#[test]
fn inherited_calls_reject_forged_nominal_paths_and_const_roots() {
    use sha2::{Digest, Sha256};
    for selected in ["call", "change"] {
        let project = Project::with_fixture("inherited.cpp", selected, INHERITED_SOURCE);
        refresh_import(&project.config()).unwrap();
        let artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let original_lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        let other = artifact["records"]
            .as_array()
            .unwrap()
            .iter()
            .find(|record| record["name"] == "Other")
            .unwrap();
        for mutation in 0..8 {
            let mut hostile = artifact.clone();
            let place = &mut hostile["functions"][0]["body"][0]["arguments"][0]["place"];
            let path = place["projections"].as_array_mut().unwrap();
            let last = path.len() - 1;
            match mutation {
                0 => path[last]["base"]["record_declaration_id"] = "unknown".into(),
                1 => {
                    path[last]["base"]["base_declaration_id"] = other["declaration_id"].clone();
                    path[last]["base"]["base_name"] = other["name"].clone();
                }
                2 => path[last]["base"]["base_name"] = "wrong".into(),
                3 => path[last]["base"]["span"]["file"] = "other.h".into(),
                4 => path.reverse(),
                5 => {
                    path.pop();
                }
                6 => {
                    path[last]["unexpected"] = true.into();
                }
                7 if selected == "change" => {
                    hostile["functions"][0]["parameters"][0]["value_type"]["pointee"]["is_const"] =
                        true.into();
                }
                7 => {
                    path.push(path[last].clone());
                }
                _ => unreachable!(),
            }
            let bytes = serde_json::to_vec(&hostile).unwrap();
            let mut lock = original_lock.clone();
            lock_source_mut(&mut lock)["artifact"]["sha256"] =
                format!("{:x}", Sha256::digest(&bytes)).into();
            lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
            fs::write(project.artifact(), bytes).unwrap();
            fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
            let error = load_import(&project.config()).unwrap_err();
            assert!(
                error.len() < 8000,
                "unbounded error for {selected}/{mutation}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn inherited_calls_reject_missing_authority_and_false_frames() {
    let project = Project::with_fixture("inherited.cpp", "call", INHERITED_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"
        verifying "inherited.cpp";
        int32 Helper(const struct Base& value) { views value.size; ensures result == value.size; }
        int32 call(const struct Envelope& state) { views state.left.base.base.size; views state.unrelated.size; ensures result == state.left.base.base.size; ensures state.unrelated.size == old(state.unrelated.size); }
    "#;
    for hostile in [
        sidecar.replace("views state.left.base.base.size;", ""),
        sidecar.replace(
            "ensures result == state.left.base.base.size;",
            "ensures result != state.left.base.base.size;",
        ),
        sidecar.replace(
            "state.unrelated.size == old(state.unrelated.size)",
            "state.unrelated.size != old(state.unrelated.size)",
        ),
    ] {
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

const SIGNED_CONVERSION_SOURCE: &str =
    include_str!("fixtures/cpp-verification/signed-conversion/conversion.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7s in the parallel gate"]
fn cpp20_unsigned_to_signed64_preserves_all_bits_at_boundaries() {
    for value in [
        0u64,
        1,
        i32::MAX as u64,
        u32::MAX as u64,
        i64::MAX as u64,
        1u64 << 63,
        (1u64 << 63) + 1,
        u64::MAX,
    ] {
        for selected in ["explicit_cast", "implicit_cast"] {
            let project =
                Project::with_fixture("conversion.cpp", selected, SIGNED_CONVERSION_SOURCE);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let expected = value as i64;
            let source = format!(
                "verifying \"conversion.cpp\"; int64 {selected}(uint64 value) {{ requires value == {value}u64; ensures result == {expected}i64; }}"
            );
            check_selected_claim_certificate(&project, &import, &source);
            let hostile = source.replace(
                &format!("result == {expected}i64"),
                &format!("result == {}i64", expected.wrapping_add(1)),
            );
            fs::write(
                project.directory.join("bad.click"),
                hostile.replace(
                    "-9223372036854775808i64",
                    "(-9223372036854775807i64 - 1i64)",
                ),
            )
            .unwrap();
            let bad = fs::read_to_string(project.directory.join("bad.click")).unwrap();
            let parsed = read_click_project(&project.directory.join("bad.click"), &bad).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn cpp20_signed_unsigned_round_trips_verify_without_input_bounds() {
    for (selected, value_type) in [
        ("signed_round_trip", "int64"),
        ("unsigned_round_trip", "uint64"),
    ] {
        let project = Project::with_fixture("conversion.cpp", selected, SIGNED_CONVERSION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"conversion.cpp\"; {value_type} {selected}({value_type} value) {{ ensures result == value; }}"
        );
        check_first_claim_certificate(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn cpp20_modular_conversion_contract_preserves_bits_and_frames_memory() {
    let project = Project::with_fixture("conversion.cpp", "relay", SIGNED_CONVERSION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "conversion.cpp";
int64 explicit_cast(uint64 value) { ensures (result as uint64) == value; }
int64 relay(uint64 value, int32* untouched) {
 owns untouched[0..1];
 ensures (result as uint64) == value;
 ensures untouched[0] == old(untouched[0]);
}
"#;
    check_first_claim_certificate(&project, &import, source);
}

#[test]
fn cpp20_conversion_keeps_following_signed_overflow_obligations() {
    let project = Project::with_fixture("conversion.cpp", "arithmetic", SIGNED_CONVERSION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_first_claim_certificate(
        &project,
        &import,
        "verifying \"conversion.cpp\"; int64 arithmetic(uint64 value) { requires value == 18446744073709551615u64; ensures result == 0i64; }",
    );
    let source = "verifying \"conversion.cpp\"; int64 arithmetic(uint64 value) { requires value == 9223372036854775807u64; ensures result == 0i64; }";
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn cpp20_fee_fast_paths_preserve_the_signed_return_conversion() {
    for (fee, at_size, size) in [
        (0u64, 1u64, 3u64),
        (7, 2, 3),
        (8, 2, 4),
        (8589934591, 2147483647, 2147483647),
    ] {
        for (selected, instance, expected) in [
            ("fee_down", "fee<true>", (fee * at_size / size) as i64),
            (
                "fee_up",
                "fee<false>",
                (fee * at_size).div_ceil(size) as i64,
            ),
        ] {
            let project =
                Project::with_fixture("conversion.cpp", selected, SIGNED_CONVERSION_SOURCE);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let contract = format!(
                "requires fee == {fee}i64; requires at_size == {at_size}; requires size == {size}; ensures result == {expected}i64;"
            );
            let caller_contract = contract.replace("requires fee ==", "requires fee_value ==");
            let source = format!(
                "verifying \"conversion.cpp\"; int64 {instance}(int64 fee, int32 at_size, int32 size) {{ {contract} }} int64 {selected}(int64 fee_value, int32 at_size, int32 size) {{ {caller_contract} }}"
            );
            check_selected_claim_certificate(&project, &import, &source);
        }
    }
}

const RETURN_CALL_SOURCE: &str = include_str!("fixtures/cpp-verification/return-call/relay.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn direct_return_calls_verify_modular_contracts_and_frame_memory() {
    let project = Project::with_fixture("relay.cpp", "relay", RETURN_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [
        CppStatement::ReturnCall {
            callee,
            arguments,
            value_type,
            cleanups,
            span,
            conversions,
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("retain a typed direct return call");
    };
    assert!(conversions.is_empty());
    assert_eq!(callee.name, "echo");
    assert_eq!(
        callee.declaration_id,
        import.export().reachable_functions[0].declaration_id
    );
    assert_eq!(arguments.len(), 1);
    assert!(matches!(
        value_type,
        CppType::Integer {
            bits: 32,
            signed: true,
            ..
        }
    ));
    assert!(cleanups.is_empty());
    assert_eq!(span.file, "relay.cpp");
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; }
int32 relay(int32 value, int32* untouched) {
 owns untouched[0..1];
 ensures result == value;
 ensures untouched[0] == old(untouched[0]);
}
"#;
    check_selected_claim_certificate(&project, &import, source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn direct_return_calls_preserve_each_scalar_type_and_branch_result() {
    for (selected, helper, value_type) in [
        ("relay64", "echo64", "int64"),
        ("relay_u32", "echo_u32", "uint32"),
        ("relay_u64", "echo_u64", "uint64"),
        ("relay_bool", "echo_bool", "bool"),
    ] {
        let project = Project::with_fixture("relay.cpp", selected, RETURN_CALL_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"relay.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} {value_type} {selected}({value_type} value) {{ ensures result == value; }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
    }
    let project = Project::with_fixture("relay.cpp", "choose", RETURN_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; }
int32 choose(bool first, int32 value) {
 ensures first == true implies result == value;
 ensures first == false implies result == 7;
}
"#;
    check_selected_claim_certificate(&project, &import, source);
}

#[test]
fn direct_return_calls_keep_internal_capture_names_fresh_and_reject_false_results() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        // A source local named `result`, the capture's own name, keeps it;
        // the capture takes the next free spelling.
        "int echo(int value) noexcept { return value; } int relay(int value) noexcept { int result = value; return echo(result); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; }
int32 relay(int32 value) { ensures result == value; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let hostile = source.replace(
        "int32 relay(int32 value) { ensures result == value; }",
        "int32 relay(int32 value) { ensures result == 7; }",
    );
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn direct_return_calls_preserve_fee_method_template_wrappers() {
    for (selected, instance, expected) in [
        (
            "FeeFrac::EvaluateFeeDown",
            "FeeFrac::EvaluateFee<true>",
            4i64,
        ),
        (
            "FeeFrac::EvaluateFeeUp",
            "FeeFrac::EvaluateFee<false>",
            5i64,
        ),
    ] {
        let project = Project::with_fixture("relay.cpp", selected, RETURN_CALL_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let contract = format!(
            "views this->fee; views this->size; requires this->fee == 7i64; requires this->size == 3; requires at_size == 2; ensures result == {expected}i64; ensures this->fee == old(this->fee); ensures this->size == old(this->size);"
        );
        let source = format!(
            "verifying \"relay.cpp\"; int64 {instance}(int32 at_size) const {{ {contract} }} int64 {selected}(int32 at_size) const {{ {contract} }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace(
            &format!("result == {expected}i64"),
            &format!("result == {}i64", expected + 1),
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn direct_return_calls_reject_unsupported_expression_positions_and_recursive_graphs() {
    for (source, diagnostic) in [
        (
            "int echo(int value) { return value; } long relay(int value) noexcept { return echo(value) + 1; }",
            "must declare noexcept",
        ),
        (
            "int echo(int value); int relay(int value) noexcept { return echo(value); }",
            "must be noexcept",
        ),
        (
            "int relay(int value) noexcept { return relay(value); }",
            "recursive C++ calls",
        ),
    ] {
        let project = Project::with_fixture("relay.cpp", "relay", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7s in the parallel gate"]
fn direct_return_calls_capture_typed_results_before_destructors() {
    check_return_cleanup_cases("int32");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn direct_return_calls_capture_boolean_results_before_destructors() {
    check_return_cleanup_cases("bool");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn direct_return_calls_capture_wide_results_before_destructors() {
    check_return_cleanup_cases("int64");
}

fn check_return_cleanup_cases(selected_type: &str) {
    let cpp = include_str!("fixtures/cpp-verification/return-call/cleanup.cpp");
    for (selected, helper, value_type, helper_parameters, helper_contract, expected) in [
        (
            "capture",
            "read",
            "int32",
            "int32* slot",
            "owns slot[0..1]; ensures result == slot[0]; ensures slot[0] == old(slot[0]);",
            "7",
        ),
        (
            "capture_nested",
            "read",
            "int32",
            "int32* slot",
            "owns slot[0..1]; ensures result == slot[0]; ensures slot[0] == old(slot[0]);",
            "7",
        ),
        (
            "capture_wide",
            "wide",
            "int64",
            "",
            "ensures result == 4294967303i64;",
            "4294967303i64",
        ),
        (
            "capture_bool",
            "is_seven",
            "bool",
            "int32* slot",
            "owns slot[0..1]; requires slot[0] == 7; ensures result == true; ensures slot[0] == old(slot[0]);",
            "true",
        ),
        ("ordinary_wide", "", "int64", "", "", "4294967303i64"),
        ("ordinary_bool", "", "bool", "", "", "true"),
    ] {
        if value_type != selected_type {
            continue;
        }
        let project = Project::with_fixture("cleanup.cpp", selected, cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let helper_definition = if helper.is_empty() {
            String::new()
        } else {
            format!("{value_type} {helper}({helper_parameters}) {{ {helper_contract} }}")
        };
        let nested_helper = if selected == "capture_nested" {
            "int32 echo(int32 value) { ensures result == value; }"
        } else {
            ""
        };
        let source = format!(
            r#"verifying "cleanup.cpp";
Restore::Restore(int32* slot) {{
 owns this->p; owns this->saved; owns slot[0..1];
 ensures this->p == slot; ensures this->saved == old(slot[0]); ensures slot[0] == 7;
 ensures separate(memory(*this), memory(this->p[0..1]));
}}
Restore::~Restore() {{
 requires separate(memory(*this), memory(this->p[0..1]));
 owns this->p; owns this->saved; owns this->p[0..1];
 ensures this->p == old(this->p); ensures this->saved == old(this->saved);
 ensures this->p[0] == old(this->saved);
}}
{helper_definition}
{nested_helper}
{value_type} {selected}(int32& value) {{
 owns value; ensures result == {expected}; ensures value == old(value);
}}
"#
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace(
            &format!("ensures result == {expected}; ensures value =="),
            &format!(
                "ensures result == {}; ensures value ==",
                if value_type == "bool" { "false" } else { "0" }
            ),
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn direct_return_calls_keep_guarded_try_returns_unsupported_and_emit_uncaught_cleanup() {
    let cpp = include_str!("fixtures/cpp-verification/return-call/unwind.cpp");
    for selected in ["caught", "caught_value"] {
        let project = Project::with_fixture("unwind.cpp", selected, cpp);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(selected, "unwind.cpp", true, "scalar_int32");
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("return from a guarded try region"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }

    // Keep this regression focused on the selected guard's structural cleanup.
    // Borrowed memory on throwing exits has separate proof/replay coverage.
    let escaping = Project::with_fixture("unwind.cpp", "escaping", cpp);
    escaping.write_exception_enabled_compilation_database();
    escaping.write_config_with_exception_behavior("escaping", "unwind.cpp", true, "scalar_int32");
    refresh_import(&escaping.config()).unwrap();
    let lowered = lower_import(&load_import(&escaping.config()).unwrap()).unwrap();
    fn has_unwind_cleanup(statement: &ProgramStatement) -> bool {
        match statement {
            ProgramStatement::UnwindCleanup { cleanup, .. } => {
                contains_call(cleanup, "Restore::~Restore")
            }
            ProgramStatement::Seq(statements) => statements
                .iter()
                .any(|statement| has_unwind_cleanup(statement)),
            _ => false,
        }
    }
    assert!(has_unwind_cleanup(lowered.kernel_function().body()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn direct_return_calls_propagate_object_free_exception_contracts() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int helper(bool should_throw) { if (should_throw) { throw 7; } return 5; } int relay(bool should_throw) { return helper(should_throw); }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "relay.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 helper(bool should_throw) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
int32 relay(bool should_throw) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let (before, after) = source
        .rsplit_once("exceptional ensures exception == 7;")
        .expect("caller has an exceptional postcondition");
    let hostile = format!("{before}exceptional ensures exception == 8;{after}");
    assert_ne!(hostile, source);
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: exceptional payload namespaces, propagation, expansion, and hostile claim"]
fn exceptional_payload_is_separate_from_cpp_source_names() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int helper(int __click_exception, int value) { if (__click_exception == 0) { throw 7; } return value; } int relay(int __click_exception, int value) { return helper(__click_exception, value); }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "relay.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 helper(int32 __click_exception, int32 value) throws int32 {
    requires __click_exception == 0;
    requires value == 3;
    exceptional ensures exception == 7 and __click_exception == 0 and value == 3 and old(value) == 3;
}
int32 relay(int32 __click_exception, int32 value) throws int32 {
    requires __click_exception == 0;
    requires value == 3;
    exceptional ensures exception == 7 and __click_exception == 0 and value == 3 and old(value) == 3;
}
"#;
    check_selected_claim_certificate(&project, &import, source);
    fs::write(project.directory.join("relay.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("relay.click"), source).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "relay.exceptional_ensures_0",
    )
    .unwrap();
    verify_program_prepared_project(
        &parsed.with_entry_source(expanded),
        load_import(&project.config()).unwrap(),
    )
    .unwrap();
    let (before, after) = source.rsplit_once("exception == 7").unwrap();
    let hostile = format!("{before}exception == 8{after}");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn nested_return_calls_verify_scalar_types_and_fresh_captures() {
    let cpp = include_str!("fixtures/cpp-verification/return-call/nested.cpp");
    for (selected, helper, value_type) in [
        ("nested", "echo", "int32"),
        ("nested64", "echo64", "int64"),
        ("nested_u32", "echo_u32", "uint32"),
        ("nested_u64", "echo_u64", "uint64"),
        ("nested_bool", "echo_bool", "bool"),
    ] {
        let project = Project::with_fixture("nested.cpp", selected, cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { arguments, .. }] =
            import.export().functions[0].body.as_slice()
        else {
            panic!("retain return call");
        };
        let [
            CppCallArgument::Call {
                callee,
                value_type: capture_type,
                span,
                ..
            },
        ] = arguments.as_slice()
        else {
            panic!("retain nested call");
        };
        assert_eq!(callee.name, helper);
        assert_eq!(span.file, "nested.cpp");
        assert_eq!(capture_type, &import.export().functions[0].return_type);
        let source = format!(
            "verifying \"nested.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} {value_type} {selected}({value_type} value) {{ ensures result == value; }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let mut hostile = source.clone();
        let result_claim = hostile.rfind("result == value").unwrap();
        hostile.replace_range(
            result_claim..result_claim + "result == value".len(),
            "result != value",
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
    let project = Project::with_fixture("nested.cpp", "collision", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 echo(int32 value) { ensures result == value; }
int32 collision(int32 __click_cpp_nested_value_0, int32 __click_cpp_nested_value_1) {
 ensures result == __click_cpp_nested_value_0;
}
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: imported runtime default and explicit override with proof replay"]
fn runtime_default_arguments_evaluate_the_helper_only_when_omitted() {
    let cpp = r#"#include "defaults.h"
int default_limit() noexcept { return 100; }
int limit(int value) noexcept { return value; }
int omitted() noexcept { return limit(); }
int overridden() noexcept { return limit(7); }
"#;
    for (selected, result, expected_calls) in [
        ("omitted", 100, &["default_limit", "limit"][..]),
        ("overridden", 7, &["limit"][..]),
    ] {
        let mut project = Project::with_fixture("default-use.cpp", selected, cpp);
        fs::write(
            project.directory.join("defaults.h"),
            "int default_limit() noexcept; int limit(int value = default_limit()) noexcept;",
        )
        .unwrap();
        if selected == "omitted" {
            project.dependencies.push("defaults.h".into());
        }
        project.write_config(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { arguments, .. }] =
            import.export().functions[0].body.as_slice()
        else {
            panic!("expected a return call to limit");
        };
        match (selected, arguments.as_slice()) {
            ("omitted", [CppCallArgument::Call { callee, span, .. }]) => {
                assert_eq!(span.file, "default-use.cpp");
                assert_eq!(span.start_line, 4);
                assert_eq!(callee.span, *span);
                assert!(
                    import
                        .export()
                        .dependencies
                        .iter()
                        .any(|name| name == "defaults.h")
                );
            }
            ("overridden", [CppCallArgument::Value { .. }]) => {
                assert!(import.export().dependencies.is_empty());
            }
            _ => panic!("expected the selected argument form"),
        }

        let lowered = lower_import(&import).unwrap();
        let mut pending = vec![lowered.kernel_function().body()];
        let mut calls = Vec::new();
        while let Some(statement) = pending.pop() {
            match statement {
                ProgramStatement::Seq(body) => pending.extend(body.iter().rev().map(AsRef::as_ref)),
                ProgramStatement::CallResult { function_name, .. } => {
                    calls.push(
                        click::surface::source_display_name(function_name)
                            .unwrap_or_else(|| function_name.clone()),
                    );
                }
                _ => {}
            }
        }
        assert_eq!(calls, expected_calls);
        let mut source = String::from(
            "verifying \"default-use.cpp\";\nint32 limit(int32 value) { ensures result == value; }\n",
        );
        if selected == "omitted" {
            source.push_str("int32 default_limit() { ensures result == 100; }\n");
        }
        source.push_str(&format!(
            "int32 {selected}() {{ ensures result == {result}; }}\n"
        ));
        check_selected_claim_certificate(&project, &import, &source);
    }

    let ambiguous = Project::with_fixture(
        "ambiguous.cpp",
        "run",
        "int next() noexcept { return 1; } int pair(int a, int b = next()) noexcept { return a; } int run() noexcept { return pair(next()); }",
    );
    let error = refresh_import(&ambiguous.config()).unwrap_err();
    assert!(error.contains("preserve evaluation order"), "{error}");
}

#[test]
fn nested_return_calls_reject_unspecified_order_conversions_and_cycles() {
    for (cpp, diagnostic) in [
        (
            "int echo(int x) noexcept { return x; } int pair(int x, int y) noexcept { return x; } int relay(int x) noexcept { return pair(echo(x), echo(x)); }",
            "preserve evaluation order",
        ),
        (
            "int echo(int x) noexcept { return x; } long wide(long x) noexcept { return x; } long relay(int x) noexcept { return wide(echo(x)); }",
            "expression observers require a normalized return, condition, or member store",
        ),
        (
            "int echo(int x) noexcept { return x; } int relay(int x) noexcept { return echo(relay(x)); }",
            "recursive C++ calls",
        ),
    ] {
        let project = Project::with_fixture("nested.cpp", "relay", cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn nested_return_calls_propagate_inner_exceptions_without_evaluating_outer_call() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int value) { return value; } int relay(bool fail) { return outer(inner(fail)); }";
    let project = Project::with_fixture("nested.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "nested.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 inner(bool fail) throws int32 {
 ensures result == 5;
 exceptional ensures exception == 7;
}
int32 outer(int32 value) { ensures result == value; }
int32 relay(bool fail) throws int32 {
 ensures result == 5;
 exceptional ensures exception == 7;
}
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn nested_return_calls_use_distinct_capture_types_across_branches() {
    let project = Project::with_fixture(
        "nested.cpp",
        "choose",
        include_str!("fixtures/cpp-verification/return-call/nested.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 echo(int32 value) { ensures result == value; }
int64 echo64(int64 value) { ensures result == value; }
int64 outer32(int32 value) { requires value == 7; ensures result == 7i64; }
int64 choose(bool first, int32 value) { requires value == 7; ensures result == 7i64; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn nested_temporary_ids_scale_with_calls_and_source_collisions() {
    let mut previous = None;
    for size in [2usize, 4, 8, 16] {
        let locals = (0..size)
            .map(|index| format!("int __click_cpp_nested_value_{index} = 0;"))
            .collect::<String>();
        let nested = format!("{}value{}", "echo(".repeat(size + 1), ")".repeat(size + 1));
        let cpp = format!(
            "int echo(int value) noexcept {{ return value; }} int relay(int value) noexcept {{ {locals} return {nested}; }}"
        );
        let project = Project::with_fixture("nested.cpp", "relay", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        // The shared constant layer charges decimal parsing at both artifact
        // validation and lowering. Each one-character initializer adds six
        // units; temporary allocation must still grow linearly across all sizes.
        assert!(
            work >= 2 * size && work <= 11 * size + 32,
            "{size} calls and collisions: {work} work"
        );
        if let Some(previous) = previous {
            assert!(
                work <= previous * 2,
                "doubling calls must not exceed twice the work"
            );
        }
        previous = Some(work);
    }
}

const MULTIPLE_ARGUMENTS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/return-call/multiple-arguments.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn nested_calls_with_stable_siblings_preserve_each_argument_position_and_casts() {
    for (selected, outer, slot) in [
        ("nested_first", "first", "a"),
        ("literal_siblings", "first", "a"),
        ("nested_second", "second", "b"),
        ("nested_third", "third", "c"),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arguments.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} int32 {outer}(int32 a, int32 b, int32 c) {{ ensures result == {slot}; }} int32 {selected}(int32 value) {{ ensures result == value; }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let [CppStatement::ReturnCall { arguments, .. }] =
            import.export().functions[0].body.as_slice()
        else {
            panic!("retain return call");
        };
        assert_eq!(arguments.len(), 3);
        assert_eq!(
            arguments
                .iter()
                .filter(|arg| matches!(arg, CppCallArgument::Call { .. }))
                .count(),
            1
        );
    }
    for (selected, outer, inner, value_type) in [
        (
            "nested_unsigned",
            "pick_unsigned",
            "echo_unsigned",
            "uint32",
        ),
        ("nested_bool", "pick_bool", "echo_bool", "bool"),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"arguments.cpp\"; {value_type} {inner}({value_type} value) {{ ensures result == value; }} {value_type} {outer}({value_type} left, {value_type} right) {{ ensures result == right; }} {value_type} {selected}({value_type} value, int32 other) {{ ensures result == value; }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn nested_calls_with_stable_siblings_preserve_fee_rounding_pattern() {
    for (fee, round_down, expected) in [
        (7, true, 4),
        (7, false, 5),
        (-7, true, -5),
        (-7, false, -4),
        (10, true, 6),
        (10, false, 6),
    ] {
        let project =
            Project::with_fixture("arguments.cpp", "EvaluateFee", MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let product = fee * 3;
        let down = round_down;
        let source = format!(
            r#"verifying "arguments.cpp";
int64 Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }}
int64 Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }}
int64 EvaluateFee(int64 fee, int32 at_size, int32 divisor, bool round_down) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; requires round_down == {down}; ensures result == {expected}i64; }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
        let mut hostile = source.clone();
        let claim = format!("result == {expected}i64");
        let start = hostile.rfind(&claim).unwrap();
        hostile.replace_range(
            start..start + claim.len(),
            &format!("result == {}i64", expected + 1),
        );
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn sibling_observer_arguments_require_read_only_contracts_in_throwing_callers() {
    let project = Project::with_fixture(
        "observers.cpp",
        "probe",
        r#"
struct Count {
    unsigned long value;
    unsigned long size() const noexcept { return value; }
    unsigned long accept(unsigned long input) const noexcept { return input; }
};
struct Reader { Count source; };
void sink(unsigned long left, unsigned long right) noexcept { return; }
unsigned long probe(const Reader& reader, const Count& dst, bool fail) {
    if (fail) { throw 7; }
    sink(reader.source.size(), dst.size());
    return reader.source.accept(dst.size());
}
"#,
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("probe", "observers.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "observers.cpp";
uint64 Count::size() const {
    views this->value;
    ensures result == this->value;
}
uint64 Count::accept(uint64 input) const {
    ensures result == input;
}
void sink(uint64 left, uint64 right) {
    requires left <= right;
    ensures true;
}
uint64 probe(const Reader& reader, const Count& dst, bool fail) throws int32 {
    views reader.source.value;
    views dst.value;
    requires reader.source.value <= dst.value;
    ensures not fail;
    ensures result == dst.value;
    exceptional ensures fail;
    exceptional ensures exception == 7;
}
"#;
    check_selected_claim_certificate(&project, &import, proof);

    let sidecar = project.directory.join("observers.click");
    fs::write(&sidecar, proof).unwrap();
    for (edited, expected) in [
        (
            proof.replace("views this->value;", "owns this->value;"),
            "requires a read-only contract",
        ),
        (
            proof.replace("Count::size() const {", "Count::size() const diverges {"),
            "requires a terminating contract",
        ),
    ] {
        let parsed = read_click_project(&sidecar, &edited).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(error.report().contains(expected), "{}", error.report());
    }
}

#[test]
fn nested_calls_reject_sibling_memory_reads_effects_arithmetic_and_other_calls() {
    for cpp in [
        "int mutate(int& x) noexcept { x = 7; return x; } int pair(int a, int b) noexcept { return a; } int relay(int& x) noexcept { return pair(mutate(x), x); }",
        "int mutate(int* x) noexcept { *x = 7; return *x; } int pair(int a, int b) noexcept { return a; } int relay(int* x) noexcept { return pair(mutate(x), *x); }",
        "struct Box { int value; }; int mutate(Box& box) noexcept { box.value = 7; return box.value; } int pair(int a, int b) noexcept { return a; } int relay(Box& box) noexcept { return pair(mutate(box), box.value); }",
        "int echo(int x) noexcept { return x; } int pair(int a, int b) noexcept { return a; } int relay(int x) noexcept { return pair(echo(x), echo(x)); }",
        "int echo(int x) noexcept { return x; } int pair(int a, int b) noexcept { return a; } int relay(int x) noexcept { return pair(echo(x), x + 1); }",
        "int echo(int x) noexcept { return x; } int pair(int a, int b) noexcept { return a; } int relay(int x) noexcept { return pair(echo(x), ++x); }",
    ] {
        let project = Project::with_fixture("arguments.cpp", "relay", cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("preserve evaluation order"), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn nested_calls_with_stable_siblings_propagate_inner_exceptions() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int left, int value, bool flag) { return value; } int relay(bool fail, int left) { return outer(left, inner(fail), fail); }";
    let project = Project::with_fixture("arguments.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "arguments.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 inner(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
int32 outer(int32 left, int32 value, bool flag) { ensures result == value; }
int32 relay(bool fail, int32 left) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn nested_argument_lowering_scales_with_arity() {
    let mut previous = None;
    for size in [2usize, 8, 32, 128] {
        let parameters = (0..size)
            .map(|i| format!("int a{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = std::iter::once("inner()".to_string())
            .chain((1..size).map(|_| "7".to_string()))
            .collect::<Vec<_>>()
            .join(", ");
        let cpp = format!(
            "int inner() noexcept {{ return 7; }} int outer({parameters}) noexcept {{ return a0; }} int relay() noexcept {{ return outer({arguments}); }}"
        );
        let project = Project::with_fixture("arguments.cpp", "relay", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        // One-character literals now pay six units for shared checked parsing
        // at the two import boundaries. Retain the multi-size growth check.
        assert!(
            work >= size && work <= 9 * size + 32,
            "{size} arguments: {work} work"
        );
        if let Some(previous) = previous {
            assert!(
                work <= previous * 4,
                "quadrupling arity must not exceed four times the work"
            );
        }
        previous = Some(work);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: sibling observer argument scaling"]
fn sibling_observer_argument_lowering_scales_with_arity() {
    let mut previous = None;
    for size in [2usize, 8, 32, 128] {
        let parameters = (0..size)
            .map(|i| format!("int a{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = vec!["box.get()"; size].join(", ");
        let cpp = format!(
            "struct Box {{ int value; int get() const noexcept {{ return value; }} }}; int sink({parameters}) noexcept {{ return a0; }} int probe(const Box& box) noexcept {{ return sink({arguments}); }}"
        );
        let project = Project::with_fixture("arguments.cpp", "probe", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(work >= size, "{size} observer arguments: {work} work");
        if let Some(previous) = previous {
            assert!(
                work <= previous * 4,
                "{size} observer arguments: {work} work"
            );
        }
        previous = Some(work);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn stable_siblings_remain_valid_when_the_nested_call_writes_memory() {
    let project = Project::with_fixture(
        "arguments.cpp",
        "effectful_inner",
        MULTIPLE_ARGUMENTS_SOURCE,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 write_seven(int32* slot) {
 owns slot[0..1]; ensures slot[0] == 7; ensures result == 7;
}
int32 second(int32 a, int32 b, int32 c) { ensures result == b; }
int32 effectful_inner(int32* slot, int32 saved_value) {
 owns slot[0..1]; ensures slot[0] == 7; ensures result == 7;
}
"#,
    );
}

#[test]
fn fee_pattern_contracts_reject_zero_divisors_and_unproved_product_bounds() {
    for (selected, source) in [
        (
            "Div",
            "verifying \"arguments.cpp\"; int64 Div(int64 n, int32 d, bool round_down) { requires n == 21i64; requires d == 0; ensures result == result; }",
        ),
        (
            "Mul",
            "verifying \"arguments.cpp\"; int64 Mul(int64 fee, int32 at_size) { requires fee == 9223372036854775807i64; requires at_size == 3; ensures result == result; }",
        ),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        fs::write(project.directory.join("bad.click"), source).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn stable_constant_siblings_reject_noninline_external_linkage_and_mutable_globals() {
    for declaration in ["extern constexpr long value = 7;", "long value = 7;"] {
        let cpp = format!(
            "{declaration} int inner() noexcept {{ return 5; }} long outer(int first, long second) noexcept {{ return second; }} long relay() noexcept {{ return outer(inner(), value); }}"
        );
        let project = Project::with_fixture("arguments.cpp", "relay", &cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(!project.artifact().exists());
        assert!(
            error.contains("constexpr") || error.contains("preserve evaluation order"),
            "{error}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn scalar_local_siblings_survive_nested_memory_effects() {
    let project =
        Project::with_fixture("arguments.cpp", "local_sibling", MULTIPLE_ARGUMENTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 write_seven(int32* slot) { owns slot[0..1]; ensures slot[0] == 7; ensures result == 7; }
int32 first(int32 a, int32 b, int32 c) { ensures result == a; }
int32 local_sibling(int32* slot, int32 value) { owns slot[0..1]; ensures slot[0] == 7; ensures result == value; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn nested_stable_siblings_preserve_concrete_boolean_template_rounding_wrappers() {
    for (selected, down, fee, expected) in [
        ("fee_down", true, 7, 4),
        ("fee_up", false, 7, 5),
        ("fee_down", true, -7, -5),
        ("fee_up", false, -7, -4),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] =
            import.export().functions[0].body.as_slice()
        else {
            panic!("retain template return call");
        };
        let instance = &cpp_spelling(&import, &callee.declaration_id);
        let product = fee * 3;
        let source = format!(
            r#"verifying "arguments.cpp";
int64 Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }}
int64 Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }}
int64 {instance}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }}
int64 {selected}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }}
"#
        );
        check_selected_claim_certificate(&project, &import, &source);
    }
}

const STATIC_HELPERS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/return-call/static-helpers.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn static_helpers_preserve_scalar_types_class_identity_and_no_receiver() {
    for (member, value_type) in [
        ("echo", "int32"),
        ("echo64", "int64"),
        ("echo_u32", "uint32"),
        ("echo_u64", "uint64"),
        ("echo_bool", "bool"),
    ] {
        let project = Project::with_fixture(
            "static.cpp",
            &format!("Scalar::{member}"),
            STATIC_HELPERS_SOURCE,
        );
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert!(matches!(&import.export().functions[0].function_kind,
            CppFunctionKind::StaticMethod { record_name, record_declaration_id }
            if record_name == "Scalar" && !record_declaration_id.is_empty()));
        assert_eq!(import.export().functions[0].parameters.len(), 1);
        assert!(import.export().records.is_empty());
        let source = format!(
            "verifying \"static.cpp\"; static {value_type} Scalar::{member}({value_type} value) {{ ensures result == value; }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace("result == value", "result != value");
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn static_helpers_support_modular_nested_and_initializer_calls() {
    for selected in ["static_chain", "static_local"] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            r#"verifying "static.cpp";
static int32 Scalar::echo(int32 value) {{ ensures result == value; }}
static int32 Other::echo(int32 value) {{ ensures result == value; }}
int32 {selected}(int32 value) {{ ensures result == value; }}
"#
        );
        // The local caller reaches only Scalar::echo.
        let source = if selected == "static_local" {
            source.replace(
                "static int32 Other::echo(int32 value) { ensures result == value; }\n",
                "",
            )
        } else {
            source
        };
        check_selected_claim_certificate(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn static_helpers_preserve_nested_fee_rounding_template_shape() {
    for (selected, down, fee, expected) in [
        ("static_fee_down", true, 7, 4),
        ("static_fee_up", false, 7, 5),
        ("static_fee_down", true, -7, -5),
        ("static_fee_up", false, -7, -4),
    ] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] =
            import.export().functions[0].body.as_slice()
        else {
            panic!("static template call");
        };
        let product = fee * 3;
        let instance = &cpp_spelling(&import, &callee.declaration_id);
        let source = format!(
            r#"verifying "static.cpp";
static int64 FeeMath::Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }}
static int64 FeeMath::Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }}
static int64 {instance}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }}
int64 {selected}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }}
"#
        );
        check_selected_claim_certificate(&project, &import, &source);
    }
}

#[test]
fn static_helpers_reject_object_dispatch_reference_parameters_and_recursion() {
    for (cpp, selected, diagnostic) in [
        (
            "struct H { int storage; static int echo(int x) noexcept { return x; } }; int relay(H& h, int x) noexcept { return h.echo(x); }",
            "relay",
            "class-qualified or unqualified",
        ),
        (
            "struct H { static int echo(int x) noexcept { return x; } }; int relay(int x) noexcept { return H{}.echo(x); }",
            "relay",
            "class-qualified or unqualified",
        ),
        (
            "struct H { static int echo(int x) noexcept { return x; } }; int relay(int x) noexcept { return ((void)++x, H{}).echo(x); }",
            "relay",
            "class-qualified or unqualified",
        ),
        (
            "struct H { static int read(const int& x) noexcept { return x; } };",
            "H::read",
            "by-value scalar",
        ),
        (
            "struct H { static int read(int* x) noexcept { return *x; } };",
            "H::read",
            "by-value scalar",
        ),
        (
            "struct H { static int recurse(int x) noexcept { return recurse(x); } };",
            "H::recurse",
            "recursive C++ calls",
        ),
    ] {
        let project = Project::with_fixture("static.cpp", selected, cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn static_helpers_propagate_scalar_exceptions_through_nested_calls() {
    let cpp = "struct H { static int inner(bool fail) { if (fail) { throw 7; } return 5; } static int outer(int value) { return value; } static int relay(bool fail) { return outer(inner(fail)); } };";
    let project = Project::with_fixture("static.cpp", "H::relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("H::relay", "static.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "static.cpp";
static int32 H::inner(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
static int32 H::outer(int32 value) { ensures result == value; }
static int32 H::relay(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn static_helpers_called_from_value_methods_preserve_field_authority() {
    let project = Project::with_fixture("static.cpp", "FeeValue::Evaluate", STATIC_HELPERS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "static.cpp";
static int64 FeeMath::Mul(int64 fee, int32 at_size) { requires fee == 7i64; requires at_size == 3; ensures result == 21i64; }
int64 FeeValue::Evaluate(int32 at_size) const {
 owns this->fee;
 requires this->fee == 7i64;
 requires at_size == 3;
 ensures result == 21i64;
 ensures this->fee == old(this->fee);
}
"#;
    check_selected_claim_certificate(&project, &import, source);
    let hostile = source.replace(" owns this->fee;\n", "");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn static_helpers_cannot_skip_arithmetic_definedness_with_trivial_postconditions() {
    for (selected, contract) in [
        (
            "FeeMath::Mul",
            "static int64 FeeMath::Mul(int64 fee, int32 at_size) { ensures result == result; }",
        ),
        (
            "FeeMath::Div",
            "static int64 FeeMath::Div(int64 n, int32 d, bool round_down) { ensures result == result; }",
        ),
    ] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!("verifying \"static.cpp\"; {contract}");
        fs::write(project.directory.join("bad.click"), &source).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &source).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

const NORMALIZED_EVALUATION_SOURCE: &str =
    include_str!("fixtures/cpp-verification/return-call/normalized-evaluation.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn normalized_scalar_calls_agree_across_returns_initializers_and_discarded_results() {
    for (selected, contract) in [
        (
            "direct",
            "int32 direct(int32 value, int32 sibling) { ensures result == value; }",
        ),
        (
            "initialized",
            "int32 initialized(int32 value, int32 sibling) { ensures result == value; }",
        ),
        (
            "discarded",
            "int32 discarded(int32 value) { ensures result == value; }",
        ),
    ] {
        let project =
            Project::with_fixture("evaluation.cpp", selected, NORMALIZED_EVALUATION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let helpers = if selected == "discarded" {
            ""
        } else {
            "int32 first(int32 value, int32 sibling) { ensures result == value; }"
        };
        let source = format!(
            "verifying \"evaluation.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} {helpers} {contract}"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace("ensures result == value", "ensures result != value");
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn normalized_initializer_calls_preserve_scalar_types_and_static_helpers() {
    for (selected, helper, value_type, storage) in [
        ("initialized64", "echo64", "int64", ""),
        ("initialized_u32", "echo_u32", "uint32", ""),
        ("initialized_u64", "echo_u64", "uint64", ""),
        ("Helper::initialized", "Helper::echo", "int32", "static "),
    ] {
        let project =
            Project::with_fixture("evaluation.cpp", selected, NORMALIZED_EVALUATION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"evaluation.cpp\"; {storage}{value_type} {helper}({value_type} value) {{ ensures result == value; }} {storage}{value_type} {selected}({value_type} value) {{ ensures result == value; }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn normalized_initializer_calls_capture_before_normal_cleanup() {
    let project = Project::with_fixture(
        "evaluation.cpp",
        "initialized_cleanup",
        NORMALIZED_EVALUATION_SOURCE,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    // Reuse the existing independently checked constructor/destructor contracts.
    let source = r#"verifying "evaluation.cpp";
Restore::Restore(int32* value) {
 owns this->slot; owns this->saved; owns value[0..1];
 ensures this->slot == value;
 ensures this->saved == old(value[0]);
 ensures value[0] == 7;
 ensures separate(memory(*this), memory(this->slot[0..1]));
}
Restore::~Restore() {
 requires separate(memory(*this), memory(this->slot[0..1]));
 owns this->slot; owns this->saved; owns this->slot[0..1];
 ensures this->slot == old(this->slot);
 ensures this->saved == old(this->saved);
 ensures this->slot[0] == old(this->saved);
}
int32 read(int32* slot) { owns slot[0..1]; ensures result == old(slot[0]); ensures slot[0] == old(slot[0]); }
int32 echo(int32 value) { ensures result == value; }
int32 initialized_cleanup(int32& value) { owns value; ensures result == 7; ensures value == old(value); }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let lowered = lower_import(&import).unwrap();
    assert_eq!(
        lowered.contract_functions().len(),
        import.export().reachable_functions.len() + 1
    );
    assert!(lowered.record_layouts().contains_key("Restore"));
    let caller = lowered
        .contract_functions()
        .iter()
        .find(|f| f.name() == "initialized_cleanup")
        .unwrap();
    assert_eq!(
        caller
            .local_struct_values()
            .get(&("guard").into())
            .map(String::as_str),
        Some("Restore")
    );
}

#[test]
fn normalized_call_order_rejections_are_independent_of_source_context() {
    for body in [
        "return first(echo(value), *slot);",
        "int captured = first(echo(value), *slot); return captured;",
        "first(echo(value), *slot); return value;",
    ] {
        let cpp = format!(
            "int echo(int value) noexcept {{ return value; }} int first(int value, int sibling) noexcept {{ return value; }} int relay(int value, int* slot) noexcept {{ {body} }}"
        );
        let project = Project::with_fixture("evaluation.cpp", "relay", &cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("preserve evaluation order"), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn normalized_initializer_calls_propagate_inner_exceptions() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int value) { return value; } int relay(bool fail) { int captured = outer(inner(fail)); return captured; }";
    let project = Project::with_fixture("evaluation.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "evaluation.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "evaluation.cpp";
int32 inner(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
int32 outer(int32 value) { ensures result == value; }
int32 relay(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn normalized_initializer_and_return_work_scales_with_argument_arity() {
    let mut overhead = None;
    for size in [2usize, 8, 32, 128] {
        let parameters = (0..size)
            .map(|i| format!("int value{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = (0..size)
            .map(|i| {
                if i == size / 2 {
                    "echo(value)".into()
                } else {
                    "value".into()
                }
            })
            .collect::<Vec<String>>()
            .join(", ");
        let cpp = format!(
            "int echo(int value) noexcept {{ return value; }} int first({parameters}) noexcept {{ return value0; }} int direct(int value) noexcept {{ return first({arguments}); }} int initialized(int value) noexcept {{ int captured = first({arguments}); return captured; }}"
        );
        let mut measured = Vec::new();
        for selected in ["direct", "initialized"] {
            let project = Project::with_fixture("evaluation.cpp", selected, &cpp);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let (lowered, work) =
                click::instrumentation::measure_deterministic_work(|| lower_import(&import));
            let lowered = lowered.unwrap();
            assert_eq!(lowered.contract_functions().len(), 3);
            assert!(
                work >= size && work <= 4 * size + 32,
                "{selected}, arity {size}: {work}"
            );
            measured.push(work);
        }
        let delta = measured[1].checked_sub(measured[0]).unwrap();
        assert!((1..=8).contains(&delta), "initializer overhead: {delta}");
        assert_eq!(
            *overhead.get_or_insert(delta),
            delta,
            "initializer overhead must remain constant at arity {size}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn lifetime_returns_destroy_only_the_objects_constructed_on_that_path() {
    let cpp =
        include_str!("fixtures/cpp-verification/reverse-destructor-order/construction_prefix.cpp");
    let project = Project::with_fixture("restore_twice.cpp", "construction_prefix", cpp);
    refresh_import(&project.config()).expect("export an early return before a later construction");
    let import = load_import(&project.config()).unwrap();
    let [
        CppStatement::Declare { .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Declare { .. },
        CppStatement::Assign { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("construction events must retain their source order");
    };
    let [
        CppStatement::Return {
            cleanups: early_cleanups,
            ..
        },
    ] = then_branch.as_slice()
    else {
        panic!("early return cleanup edge");
    };
    assert_eq!(early_cleanups.len(), 1);
    assert_eq!(final_cleanups.len(), 2);
    let source = REVERSE_DESTRUCTOR_SIDECAR.replace("restore_twice(", "construction_prefix(");
    check_selected_claim_certificate(&project, &import, &source);
    let false_claim = source.replace(
        "early == true implies result == 7",
        "early == true implies result == 9",
    );
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &false_claim).unwrap();
    let false_project = read_click_project(&sidecar, &false_claim).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a future object cannot change the early return result");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn lifetime_return_before_any_construction_has_no_cleanup() {
    let cpp =
        include_str!("fixtures/cpp-verification/reverse-destructor-order/construction_prefix.cpp");
    let project = Project::with_fixture("restore_twice.cpp", "before_construction", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [
        CppStatement::If { then_branch, .. },
        CppStatement::Declare { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().functions[0].body.as_slice()
    else {
        panic!("source construction order");
    };
    let [CppStatement::Return { cleanups, .. }] = then_branch.as_slice() else {
        panic!("early return");
    };
    assert!(cleanups.is_empty());
    assert_eq!(final_cleanups.len(), 1);
    let source = REVERSE_DESTRUCTOR_SIDECAR
        .replace("restore_twice(", "before_construction(")
        .replace(
            "early == true implies result == 7",
            "early == true implies result == old(value)",
        )
        .replace(
            "early == false implies result == 9",
            "early == false implies result == 7",
        );
    check_selected_claim_certificate(&project, &import, &source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn resolved_declaration_identities_bind_overloads_scopes_and_equal_width_types() {
    let project = Project::with_fixture(
        "identity.cpp",
        "relay",
        include_str!("fixtures/cpp-verification/declaration-identity/identity.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let helpers = &import.export().reachable_functions;
    assert_eq!(helpers.len(), 6);
    let names = helpers
        .iter()
        .map(|function| lowered.contract_name(&function.declaration_id).unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(names.len(), helpers.len());
    assert_eq!(lowered.kernel_function().name(), "relay");
    let mut sidecar = String::from("verifying \"identity.cpp\";\n");
    for helper in helpers {
        let [
            CppStatement::Return {
                value: CppExpression::IntegerLiteral { value, .. },
                ..
            },
        ] = helper.body.as_slice()
        else {
            panic!("constant helper body: {:?}", helper.body);
        };
        let name = lowered.contract_name(&helper.declaration_id).unwrap();
        let parameter_type = match helper.parameters[0].value_type {
            CppType::Integer {
                bits: 64,
                signed: true,
                ..
            } => "int64",
            _ => "int32",
        };
        sidecar.push_str(&format!(
            "int32 {name}({parameter_type} x) {{ ensures result == {value}; }}\n"
        ));
        assert!(
            lowered
                .contract_functions()
                .iter()
                .any(|function| function.name() == name)
        );
        assert!(
            lowered
                .reachable_kernel_functions()
                .iter()
                .any(|function| function.name() == name)
        );
    }
    sidecar.push_str("int32 relay(int64 x, int64 y, int32 z) { ensures result == 76; }\n");
    check_selected_claim_certificate(&project, &import, &sidecar);
    let false_claim = sidecar.replace("result == 76", "result == 74");
    let path = project.directory.join("wrong.click");
    fs::write(&path, &false_claim).unwrap();
    let parsed = read_click_project(&path, &false_claim).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn qualified_namespace_selection_has_an_ordinary_readable_contract_name() {
    let project = Project::with_fixture(
        "namespace.cpp",
        "A::Nested::echo",
        "namespace A { namespace Nested { int echo(int x) noexcept { return x; } } } int echo(int x) noexcept { return 3; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    assert_eq!(
        click::surface::source_display_name(lowered.kernel_function().name()).as_deref(),
        Some("A::Nested::echo")
    );
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"namespace.cpp\"; int32 A::Nested::echo(int32 x) { ensures result == x; }",
    );
}

#[test]
fn selected_function_collision_uses_the_same_identity_binding_as_its_helper() {
    let project = Project::with_fixture(
        "selected.cpp",
        "H_same",
        "struct H { static int same(int x) noexcept { return 5; } }; int H_same(int x) noexcept { return H::same(x); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let selected = lowered
        .contract_name(&import.export().functions[0].declaration_id)
        .unwrap();
    let helper = lowered
        .contract_name(&import.export().reachable_functions[0].declaration_id)
        .unwrap();
    assert_ne!(selected, helper);
    assert_eq!(lowered.kernel_function().name(), selected);
    let sidecar = format!(
        "verifying \"selected.cpp\"; int32 {helper}(int32 x) {{ ensures result == 5; }} int32 {selected}(int32 x) {{ ensures result == 5; }}"
    );
    check_sidecar_tactic(&project, &import, &sidecar, Some(&format!("{selected}.")));
}

#[test]
fn anonymous_namespace_helper_is_named_by_its_path() {
    let project = Project::with_fixture(
        "anonymous.cpp",
        "relay",
        "namespace { int same(int x) noexcept { return x; } } int relay(int x) noexcept { return same(x); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let name = lowered
        .contract_name(&import.export().reachable_functions[0].declaration_id)
        .unwrap();
    assert_eq!(
        click::surface::source_display_name(name).as_deref(),
        Some("(anonymous namespace)::same")
    );
    let sidecar = format!(
        "verifying \"anonymous.cpp\"; int32 {name}(int32 x) {{ ensures result == x; }} int32 relay(int32 x) {{ ensures result == x; }}"
    );
    check_selected_claim_certificate(&project, &import, &sidecar);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn bounded_constant_forests_scale_without_expanding_dependency_chains() {
    for size in [4usize, 16, 64, 256] {
        let mut cpp =
            String::from("static constexpr long long C0 = 1; static constexpr long long C1 = 3;\n");
        for index in 2..size {
            cpp.push_str(&format!(
                "static constexpr long long C{index} = 1 * C{};\n",
                index - 2
            ));
        }
        cpp.push_str(&format!(
            "long long total() noexcept {{ return C{} + C{}; }}\n",
            size - 2,
            size - 1
        ));
        let project = Project::with_fixture("forest.cpp", "total", &cpp);
        refresh_import(&project.config()).unwrap();
        let (import, validation_work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert_eq!(import.export().constants.len(), size);
        let artifact_bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
        assert!(
            validation_work >= artifact_bytes && validation_work <= artifact_bytes + 8 * size + 100,
            "{size} constants: {validation_work} work for {artifact_bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(
            work >= size && work <= 4 * size + 32,
            "{size} constants: {work} lowering work"
        );
        check_return_call_sidecar(
            &project,
            &import,
            "verifying \"forest.cpp\"; int64 total() { ensures result == 4i64; }",
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn record_inventories_and_function_lowering_share_indexes_across_sizes() {
    for size in [2usize, 8, 32, 128] {
        let mut cpp = String::new();
        let mut sidecar = String::from("verifying \"records.cpp\";\n");
        for index in 0..size {
            cpp.push_str(&format!("struct R{index} {{ int value; }}; int read{index}(int x) noexcept {{ R{index} local{{x}}; return local.value; }}\n"));
            sidecar.push_str(&format!(
                "int32 read{index}(int32 x) {{ ensures result == x; }}\n"
            ));
        }
        cpp.push_str("int relay(int x) noexcept {\n");
        for index in 0..size {
            cpp.push_str(&format!("int y{index} = read{index}(x);\n"));
        }
        cpp.push_str(&format!("return y{}; }}\n", size - 1));
        sidecar.push_str("int32 relay(int32 x) { ensures result == x; }\n");
        let project = Project::with_fixture("records.cpp", "relay", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert_eq!(import.export().records.len(), size);
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        let lowered = lowered.unwrap();
        assert_eq!(lowered.record_layouts().len(), size);
        assert!(
            work >= size && work <= 24 * size + 32,
            "{size} records/functions: {work} work"
        );
        // Small graphs exercise certificates and audit; larger graphs measure the
        // frontend inventory representation without duplicating every proof run.
        if size <= 8 {
            check_selected_claim_certificate(&project, &import, &sidecar);
            if size == 2 {
                let false_claim = sidecar.replace(
                    "int32 relay(int32 x) { ensures result == x; }",
                    "int32 relay(int32 x) { requires x == 7; ensures result == 8; }",
                );
                let path = project.directory.join("wrong.click");
                fs::write(&path, &false_claim).unwrap();
                let parsed = read_click_project(&path, &false_claim).unwrap();
                assert!(verify_program_prepared_project(&parsed, &import).is_err());
            }
        }
    }
}

#[test]
fn exporter_reports_named_inventory_budgets_and_keeps_outputs_atomic() {
    let declarations = (0..1025usize)
        .map(|index| {
            if index == 0 {
                "static constexpr long long C0 = 1;\n".to_owned()
            } else {
                format!(
                    "static constexpr long long C{index} = 1 * C{};\n",
                    index - 1
                )
            }
        })
        .collect::<String>();
    let project = Project::with_fixture(
        "budget.cpp",
        "total",
        &format!("{declarations}long long total() noexcept {{ return C1024; }}"),
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("artifact budget exhausted: constant declarations"),
        "{error}"
    );
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

#[test]
fn exporter_bounds_record_and_function_discovery_independently() {
    for (size, records, expected) in [
        (257usize, true, "record declarations"),
        (1024, false, "function declarations"),
    ] {
        let mut cpp = String::new();
        for index in 0..size {
            if records {
                cpp.push_str(&format!("struct R{index} {{ int value; }}; int f{index}(int x) noexcept {{ R{index} local{{x}}; return local.value; }}\n"));
            } else {
                cpp.push_str(&format!("int f{index}(int x) noexcept {{ return x; }}\n"));
            }
        }
        cpp.push_str("int relay(int x) noexcept {\n");
        for index in 0..size {
            cpp.push_str(&format!("f{index}(x);\n"));
        }
        cpp.push_str("return x; }");
        let project = Project::with_fixture("budget.cpp", "relay", &cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains(&format!("artifact budget exhausted: {expected}")),
            "{error}"
        );
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn distinct_record_layouts_keep_field_widths_offsets_and_ownership() {
    let project = Project::with_fixture(
        "layouts.cpp",
        "choose",
        "struct First { int value; }; struct Second { int padding; long long value; }; long long choose(First& first, Second& second) noexcept { first.value = 7; return second.value; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().records.len(), 2);
    let first = import
        .export()
        .records
        .iter()
        .find(|record| record.name == "First")
        .unwrap();
    let second = import
        .export()
        .records
        .iter()
        .find(|record| record.name == "Second")
        .unwrap();
    assert_eq!(
        (
            first.size_bytes,
            first.fields[0].offset_bytes,
            first.fields[0].size_bytes
        ),
        (4, 0, 4)
    );
    assert_eq!(
        (
            second.size_bytes,
            second.fields[1].offset_bytes,
            second.fields[1].size_bytes
        ),
        (16, 8, 8)
    );
    let sidecar = "verifying \"layouts.cpp\"; int64 choose(struct First& first, struct Second& second) { owns first.value; owns second.value; ensures first.value == 7; ensures result == old(second.value); ensures second.value == old(second.value); }";
    check_selected_claim_certificate(&project, &import, sidecar);
    let missing_authority = sidecar.replace("owns second.value;", "");
    let path = project.directory.join("wrong.click");
    fs::write(&path, &missing_authority).unwrap();
    let parsed = read_click_project(&path, &missing_authority).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

const GROWING_GUARD_SOURCE: &str = "struct Guard { int value; explicit Guard(int initial) noexcept : value(initial) {} ~Guard() noexcept { value = 0; } };\n";

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7s in the parallel gate"]
fn growing_lifetime_inventories_keep_prefix_returns_and_reverse_cleanup() {
    check_growing_lifetime_inventory("top");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn growing_sibling_lifetime_inventories_keep_prefix_returns_and_reverse_cleanup() {
    check_growing_lifetime_inventory("siblings");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 7s in the parallel gate"]
fn growing_block_lifetime_inventories_keep_prefix_returns_and_reverse_cleanup() {
    check_growing_lifetime_inventory("block");
}

fn check_growing_lifetime_inventory(mode: &str) {
    for size in [3usize, 8, 32, 128] {
        let mut body = String::new();
        if mode == "block" {
            body.push_str("{\n");
        }
        for index in 0..size {
            if mode == "siblings" {
                body.push_str("{ Guard guard(value);\n");
            } else {
                body.push_str(&format!("Guard g{index}(value);\n"));
            }
            if index == 0 {
                body.push_str("if (early) { return value; }\n");
            }
            if mode == "siblings" {
                body.push_str("}\n");
            }
        }
        if mode == "block" {
            body.push_str("}\n");
        }
        let cpp = format!(
            "{GROWING_GUARD_SOURCE}int many(bool early, int value) noexcept {{ {body} return value; }}"
        );
        let project = Project::with_fixture("guards.cpp", "many", &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = project.loaded_artifact_bytes();
        let (import, validation_work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert!(
            validation_work <= bytes + 64 * size + 256,
            "{mode}, {size}: {validation_work} validation work for {bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        let lowered = lowered.unwrap();
        assert!(
            work <= 32 * size + 128,
            "{mode}, {size}: {work} lowering work"
        );
        let order = destructor_object_order(lowered.kernel_function().body(), "Guard::~Guard");
        let expected = if mode == "siblings" {
            vec!["guard".to_string(); size + 1]
        } else {
            std::iter::once("g0".to_string())
                .chain((0..size).rev().map(|index| format!("g{index}")))
                .collect()
        };
        assert_eq!(order, expected);
        // Larger inventories check importer/lowering work; small ones also
        // exercise complete proofs, rewritten certificates, and audit.
        if size <= 8 {
            let source = r#"verifying "guards.cpp";
Guard::Guard(int32 initial) { owns this->value; ensures this->value == initial; }
Guard::~Guard() { owns this->value; ensures this->value == 0; }
int32 many(bool early, int32 value) { ensures result == value; }
"#;
            check_selected_claim_certificate(&project, &import, source);
            let hostile = source.replace(
                "ensures result == value; }",
                "requires value == 5; ensures result == 6; } by { step_until(function.exit); close(); }",
            );
            let sidecar = project.directory.join("bad.click");
            fs::write(&sidecar, &hostile).unwrap();
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(
                !error.message().contains("budget exhausted"),
                "{}",
                error.message()
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn exporter_enforces_named_lifetime_budgets_and_keeps_outputs_atomic() {
    for (kind, boundary) in [("locals", 1024usize), ("scopes", 256)] {
        for size in [boundary, boundary + 1] {
            let body = if kind == "locals" {
                (0..size)
                    .map(|index| format!("int n{index} = 0;\n"))
                    .collect::<String>()
            } else {
                "{ Guard guard(value); }\n".repeat(size)
            };
            let cpp = format!(
                "{GROWING_GUARD_SOURCE}int many(int value) noexcept {{ {body} return value; }}"
            );
            let project = Project::with_fixture("budget.cpp", "many", &cpp);
            if size == boundary {
                refresh_import(&project.config()).unwrap();
                load_import(&project.config()).unwrap();
            } else {
                let error = refresh_import(&project.config()).unwrap_err();
                let expected = if kind == "locals" {
                    "local declarations per function"
                } else {
                    "cleanup scopes per function"
                };
                assert!(
                    error.contains(&format!("artifact budget exhausted: {expected}")),
                    "{error}"
                );
                assert!(!project.artifact().exists());
                assert!(!project.lock().exists());
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn shared_scalar_interpretation_keeps_execution_and_proof_signatures_aligned() {
    for (cpp, signature, precondition, expected) in [
        (
            "long convert(unsigned long n) noexcept { return static_cast<long>(n); }",
            "int64 convert(uint64 n)",
            "n == 18446744073709551615u64",
            "-1i64",
        ),
        (
            "long convert(bool n) noexcept { return static_cast<long>(n); }",
            "int64 convert(bool n)",
            "n == true",
            "1i64",
        ),
        (
            "unsigned convert(bool n) noexcept { return static_cast<unsigned>(n); }",
            "uint32 convert(bool n)",
            "n == false",
            "0u32",
        ),
    ] {
        let project = Project::with_fixture("scalar.cpp", "convert", cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof = format!(
            "verifying \"scalar.cpp\"; {signature} {{ requires {precondition}; ensures result == {expected}; }}"
        );
        check_selected_claim_certificate(&project, &import, &proof);
        let false_value = if signature.starts_with("int64") {
            "2i64"
        } else {
            "2u32"
        };
        let hostile = proof.replace(
            &format!("ensures result == {expected};"),
            &format!("ensures result == {false_value};"),
        );
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect_err("conversion must reject a false claim");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn compiler_assumptions_require_proof_and_keep_normal_cleanup() {
    let cpp = "struct Guard { int value; explicit Guard(int n) noexcept : value(n) {} ~Guard() noexcept { value = 0; } };\nint guarded(int n) noexcept { Guard guard(n); __builtin_assume(n > 0); return n; }";
    let project = Project::with_fixture("assume.cpp", "guarded", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[1],
        CppStatement::Assume { .. }
    ));
    let contracts = r#"verifying "assume.cpp";
Guard::Guard(int32 n) { owns this->value; ensures this->value == n; }
Guard::~Guard() { owns this->value; ensures this->value == 0; }
"#;
    let source =
        format!("{contracts}\nint32 guarded(int32 n) {{ requires n > 0; ensures result == n; }}");
    check_selected_claim_certificate(&project, &import, &source);
    for requires in ["", "requires n == 0;"] {
        let hostile = source.replace("requires n > 0;", requires);
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("__builtin_assume"),
            "{}",
            error.message()
        );
    }
    let hostile = source.replace("ensures result == n;", "ensures result == n + 1;");
    let path = project.directory.join("false.click");
    fs::write(&path, &hostile).unwrap();
    let parsed = read_click_project(&path, &hostile).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .expect_err("a proved assumption cannot prove a false result");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn compiler_assumptions_cover_total_predicates_and_scale_with_statements() {
    for size in [4usize, 16, 64, 256] {
        let body = "__builtin_assume(n > 0 && bool(n));\n".repeat(size);
        let cpp = format!("int guarded(int n) noexcept {{ {body} return n; }}");
        let project = Project::with_fixture("assume.cpp", "guarded", &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = project.loaded_artifact_bytes();
        let (import, work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert!(
            work <= bytes + 64 * size + 256,
            "{size}: {work} for {bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(work <= 32 * size + 128, "{size}: {work}");
        if size == 4 {
            let proof = "verifying \"assume.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; }";
            check_return_call_sidecar(&project, &import, proof);
        }
    }
}

#[test]
fn compiler_assumptions_reject_unevaluated_effects_and_partial_or_memory_conditions() {
    for (parameters, condition) in [
        ("int n", "++n > 0"),
        ("int n", "(n = 1) > 0"),
        ("int n", "n + 1 > 0"),
        ("int n", "1 / n > 0"),
        ("int& n", "n > 0"),
        ("int* n", "*n > 0"),
    ] {
        let cpp = format!(
            "int guarded({parameters}) noexcept {{ __builtin_assume({condition}); return 1; }}"
        );
        let project = Project::with_fixture("assume.cpp", "guarded", &cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("total scalar condition"),
            "{condition}: {error}"
        );
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn user_named_assume_calls_are_not_compiler_assumptions() {
    let cpp = "void Assume(bool condition) noexcept { int ignored = 0; }\nint guarded(int n) noexcept { Assume(n > 0); return n; }";
    let project = Project::with_fixture("assume.cpp", "guarded", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[0],
        CppStatement::Call { .. }
    ));
    let proof = "verifying \"assume.cpp\"; void Assume(bool condition) { ensures condition == condition; } int32 guarded(int32 n) { ensures result == n; }";
    check_return_call_sidecar(&project, &import, proof);
    let hostile = proof.replace("ensures result == n;", "ensures n > 0;");
    let path = project.directory.join("false.click");
    fs::write(&path, &hostile).unwrap();
    let parsed = read_click_project(&path, &hostile).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .expect_err("a library spelling cannot introduce a compiler assumption");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn compiler_assumptions_preserve_conditional_execution_and_constant_reachability() {
    for (cpp, requires) in [
        (
            "int guarded(int n) noexcept { if (n > 0) { __builtin_assume(n > 0); } return n; }",
            "",
        ),
        (
            "constexpr long LIMIT = 5; int guarded(int n) noexcept { __builtin_assume(n < LIMIT); return n; }",
            "requires n == 3;",
        ),
    ] {
        let project = Project::with_fixture("assume.cpp", "guarded", cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert_eq!(
            import.export().constants.len(),
            usize::from(cpp.starts_with("constexpr"))
        );
        let proof = format!(
            "verifying \"assume.cpp\"; int32 guarded(int32 n) {{ {requires} ensures result == n; }}"
        );
        check_selected_claim_certificate(&project, &import, &proof);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn isolated_nested_calls_state_field_siblings_in_every_scalar_context() {
    let cpp = include_str!("fixtures/cpp-verification/return-call/field-siblings.cpp");
    for (selected, outer, slot, claim) in [
        ("field_first", "first", "a", "box.value"),
        ("field_second", "second", "b", "box.value"),
        ("field_third", "third", "c", "box.value"),
        ("field_initializer", "second", "b", "box.other"),
        ("field_discarded", "first", "a", "box.other"),
        ("field_cast", "second", "b", "1"),
    ] {
        let project = Project::with_fixture("fields.cpp", selected, cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let requires = if selected == "field_cast" {
            "requires box.other == 7;"
        } else {
            ""
        };
        let proof = format!(
            "verifying \"fields.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} int32 {outer}(int32 a, int32 b, int32 c) {{ ensures result == {slot}; }} int32 {selected}(const struct Box& box) {{ owns box.value; owns box.other; {requires} ensures result == {claim}; }}"
        );
        check_selected_claim_certificate(&project, &import, &proof);
        for hostile in [
            proof.replace("owns box.other;", ""),
            proof.replace(
                &format!("ensures result == {claim};"),
                &format!("ensures result == {claim} + 1;"),
            ),
        ] {
            let path = project.directory.join("hostile.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            verify_program_prepared_project(&parsed, &import)
                .expect_err("field states need authority and cannot prove false results");
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn field_siblings_preserve_fee_template_rounding_and_static_helper_shape() {
    check_field_sibling_rounding("Down");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn field_siblings_preserve_upward_fee_template_rounding_and_static_helper_shape() {
    check_field_sibling_rounding("Up");
}

fn check_field_sibling_rounding(direction: &str) {
    let cpp = include_str!("fixtures/cpp-verification/return-call/field-fee-rounding.cpp");
    for (selected, down, fee, divisor, expected) in [
        ("Down", true, 7, 5, 4),
        ("Up", false, 7, 5, 5),
        ("Down", true, -7, 5, -5),
        ("Up", false, -7, 5, -4),
        ("Down", true, 7, 3, 7),
        ("Up", false, -7, 3, -7),
    ] {
        if selected != direction {
            continue;
        }
        let project = Project::with_fixture("fields.cpp", &format!("Fee::{selected}"), cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] =
            import.export().functions[0].body.as_slice()
        else {
            panic!("retain method template call");
        };
        let instance = &cpp_spelling(&import, &callee.declaration_id);
        let product = fee * 3;
        let proof = format!(
            r#"verifying "fields.cpp";
static int64 Fee::Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }}
static int64 Fee::Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == {divisor}; requires round_down == {down}; ensures result == {expected}i64; }}
int64 {instance}(int32 at_size) const {{ owns this->fee; owns this->size; requires this->fee == {fee}i64; requires this->size == {divisor}; requires at_size == 3; ensures result == {expected}i64; }}
int64 Fee::{selected}(int32 at_size) const {{ owns this->fee; owns this->size; requires this->fee == {fee}i64; requires this->size == {divisor}; requires at_size == 3; ensures result == {expected}i64; }}
"#
        );
        check_selected_claim_certificate(&project, &import, &proof);
        let hostile = proof.replace(
            &format!("ensures result == {expected}i64;"),
            &format!("ensures result == {}i64;", expected + 1),
        );
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect_err("field ordering does not prove false rounding");
    }
}

#[test]
fn field_sibling_authority_is_checked_even_when_inner_call_throws() {
    let cpp = "struct Box { int value; }; int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int a, int b) { return b; } int relay(bool fail, const Box& box) { return outer(inner(fail), box.value); }";
    let project = Project::with_fixture("fields.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "fields.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "fields.cpp";
int32 inner(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
int32 outer(int32 a, int32 b) { ensures result == b; }
int32 relay(bool fail, const struct Box& box) throws int32 {
 requires fail == true;
 ensures result == result;
 exceptional ensures exception == 7;
}
"#;
    let path = project.directory.join("hostile.click");
    fs::write(&path, proof).unwrap();
    let parsed = read_click_project(&path, proof).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("a throwing call cannot hide an unchecked sibling read");
    assert!(
        !error.message().contains("signature mismatch"),
        "the refusal must be about the sibling read: {}",
        error.message()
    );
}

#[test]
fn isolated_field_siblings_reject_hidden_aliases_and_other_memory_reads() {
    for cpp in [
        "struct Box { int value; }; int mutate(Box& box) noexcept { box.value = 7; return 7; } int echo(int n) noexcept { return n; } int outer(int a, int b) noexcept { return b; } int relay(Box& box) noexcept { return outer(echo(mutate(box)), box.value); }",
        "struct Box { int value; }; int inner(int* slot) noexcept { *slot = 7; return 7; } int outer(int a, int b) noexcept { return b; } int relay(Box& box, int* slot) noexcept { return outer(inner(slot), box.value); }",
        "struct Box { int value; }; int echo(int n) noexcept { return n; } int outer(int a, int b) noexcept { return b; } int relay(Box& box) noexcept { return outer(echo(1), box.value + 1); }",
    ] {
        let project = Project::with_fixture("fields.cpp", "relay", cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("preserve evaluation order"), "{error}");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn field_sibling_normalization_work_scales_with_argument_arity() {
    for size in [2usize, 8, 32, 128] {
        let parameters = (0..size)
            .map(|i| format!("int a{i}"))
            .collect::<Vec<_>>()
            .join(", ");
        let arguments = std::iter::once("echo(box.value)".to_owned())
            .chain((1..size).map(|_| "box.value".to_owned()))
            .collect::<Vec<_>>()
            .join(", ");
        let cpp = format!(
            "struct Box {{ int value; }}; int echo(int n) noexcept {{ return n; }} int outer({parameters}) noexcept {{ return a0; }} int relay(const Box& box) noexcept {{ return outer({arguments}); }}"
        );
        let project = Project::with_fixture("fields.cpp", "relay", &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = project.loaded_artifact_bytes();
        let (import, work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert!(
            work <= bytes + 32 * size + 256,
            "{size}: {work} for {bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(work >= size && work <= 8 * size + 64, "{size}: {work}");
    }
}

const WIDE_INTERMEDIATES_SOURCE: &str =
    include_str!("fixtures/cpp-verification/wide-intermediates/intermediates.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn wide_intermediates_preserve_high_bits_casts_and_signed_products() {
    for (name, result_type, params, contract) in [
        (
            "product_low",
            "uint64",
            "int64 a, int64 b",
            "requires a == 4294967296i64; requires b == 4294967296i64; ensures result == 0u64;",
        ),
        (
            "product_truth",
            "bool",
            "int64 a, int64 b",
            "requires a == 4294967296i64; requires b == 4294967296i64; ensures result == true;",
        ),
        (
            "product_low",
            "uint64",
            "int64 a, int64 b",
            "requires a == -9223372036854775808i64; requires b == 2i64; ensures result == 0u64;",
        ),
        (
            "product_low",
            "uint64",
            "int64 a, int64 b",
            "requires a == -9223372036854775808i64; requires b == -1i64; ensures result == 9223372036854775808u64;",
        ),
        (
            "signed_round_trip",
            "int64",
            "int64 value",
            "ensures result == value;",
        ),
        (
            "unsigned_round_trip",
            "uint64",
            "uint64 value",
            "ensures result == value;",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_INTERMEDIATES_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let lowered = lower_import(&import).unwrap();
        assert_eq!(
            lowered.kernel_function().return_type().byte_width(),
            if result_type == "bool" { 1 } else { 8 }
        );
        let source =
            format!("verifying \"wide.cpp\"; {result_type} {name}({params}) {{ {contract} }}");
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn wide_intermediates_cannot_hide_narrow_or_wide_signed_overflow() {
    for (name, params, contract) in [
        (
            "narrow_overflow",
            "int64 a, int64 b",
            "requires a == 9223372036854775807i64; requires b == 2i64; ensures 0 == 0;",
        ),
        (
            "wide_overflow",
            "int64 a",
            "requires a == 9223372036854775807i64; ensures 0 == 0;",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_INTERMEDIATES_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let return_type = if name == "wide_overflow" {
            "bool"
        } else {
            "uint64"
        };
        let source =
            format!("verifying \"wide.cpp\"; {return_type} {name}({params}) {{ {contract} }}");
        fs::write(project.directory.join("wide.click"), &source).unwrap();
        let parsed = read_click_project(&project.directory.join("wide.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(error.message().contains("overflow"), "{}", error.message());
    }
}

#[test]
fn wide_intermediates_refuse_unimplemented_source_operations() {
    for expression in [
        "a + b",
        "a - b",
        "-a",
        "static_cast<unsigned __int128>(a) * b",
    ] {
        let source = format!(
            "bool probe(long x, long y) noexcept {{ __int128 a = x; __int128 b = y; return bool({expression}); }}"
        );
        let project = Project::with_fixture("wide.cpp", "probe", &source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("wide"), "{expression}: {error}");
        assert!(!project.artifact().exists());
    }
    for source in [
        "long probe(__int128& x) noexcept { return static_cast<long>(x); }",
        "long probe(__int128* x) noexcept { return static_cast<long>(*x); }",
        "struct Wide { __int128 x; }; long probe(Wide& x) noexcept { return static_cast<long>(x.x); }",
    ] {
        let project = Project::with_fixture("wide.cpp", "probe", source);
        assert!(refresh_import(&project.config()).is_err(), "{source}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn wide_intermediates_compiler_constants_keep_full_payloads() {
    for (name, result_type, expected, payload) in [
        (
            "constant_low",
            "uint64",
            "18446744073709551615u64",
            "340282366920938463463374607431768211455",
        ),
        (
            "constant_high_truth",
            "bool",
            "true",
            "170141183460469231731687303715884105727",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_INTERMEDIATES_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let artifact = serde_json::to_value(import.export()).unwrap();
        let initializer = &artifact["functions"][0]["body"][0]["initializer"]["value"];
        assert_eq!(initializer["kind"], "compiler_constant");
        assert_eq!(initializer["value"], payload);
        assert_eq!(initializer["value_type"]["bits"], 128);
        let source = format!(
            "verifying \"wide.cpp\"; {result_type} {name}() {{ ensures result == {expected}; }}"
        );
        check_first_claim_certificate(&project, &import, &source);
    }
}

#[test]
fn wide_intermediates_modular_calls_preserve_cast_round_trips() {
    let project = Project::with_fixture("wide.cpp", "relay", WIDE_INTERMEDIATES_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "wide.cpp";
int64 signed_round_trip(int64 value) { ensures result == value; }
int64 relay(int64 value) { ensures result == value; }
"#,
    );
}

#[test]
fn wide_intermediates_reject_false_high_bit_and_narrowing_claims() {
    for (name, return_type, expected) in [
        ("product_truth", "bool", "false"),
        ("product_low", "uint64", "1u64"),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_INTERMEDIATES_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"wide.cpp\"; {return_type} {name}(int64 a, int64 b) {{ requires a == 4294967296i64; requires b == 4294967296i64; ensures result == {expected}; }}"
        );
        fs::write(project.directory.join("wide.click"), &source).unwrap();
        let parsed = read_click_project(&project.directory.join("wide.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("unclosed goal"),
            "{}",
            error.message()
        );
    }
}

const WIDE_CONTRACTS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/wide-contracts/contracts.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn wide_contracts_observe_full_width_inputs_and_results_offline() {
    for (name, ty, params, contract) in [
        (
            "identity",
            "int128",
            "int128 value",
            "ensures to_integer(result) == to_integer(value);",
        ),
        (
            "unsigned_identity",
            "uint128",
            "uint128 value",
            "ensures to_integer(result) == to_integer(value);",
        ),
        (
            "round_trip",
            "int128",
            "int128 value",
            "ensures to_integer(result) == to_integer(value);",
        ),
        (
            "unsigned_round_trip",
            "uint128",
            "uint128 value",
            "ensures to_integer(result) == to_integer(value);",
        ),
        (
            "maximum",
            "uint128",
            "",
            "ensures to_integer(result) == 340282366920938463463374607431768211455;",
        ),
        (
            "minimum",
            "int128",
            "",
            "ensures to_integer(result) == -170141183460469231731687303715884105728;",
        ),
        (
            "widen",
            "int128",
            "int64 value",
            "ensures to_integer(result) == to_integer(value);",
        ),
        (
            "widen_unsigned",
            "uint128",
            "uint64 value",
            "ensures to_integer(result) == to_integer(value);",
        ),
        (
            "multiply",
            "int128",
            "int64 a, int64 b",
            "requires a == 4294967296i64; requires b == 4294967296i64; ensures to_integer(result) == 18446744073709551616;",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_CONTRACTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert_eq!(
            lower_import(&import)
                .unwrap()
                .kernel_function()
                .return_type()
                .byte_width(),
            16
        );
        let source = format!("verifying \"wide.cpp\"; {ty} {name}({params}) {{ {contract} }}");
        check_first_claim_certificate(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn wide_contracts_compose_modular_calls_and_frame_narrow_memory() {
    let project = Project::with_fixture("wide.cpp", "relay", WIDE_CONTRACTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "wide.cpp";
int128 identity(int128 value) { ensures to_integer(result) == to_integer(value); }
int128 relay(int128 value, int32& untouched) {
    owns untouched;
    ensures to_integer(result) == to_integer(value);
    ensures untouched == old(untouched);
}
"#;
    check_selected_claim_certificate(&project, &import, source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn wide_contracts_reject_high_bit_false_claims() {
    for (name, ty, value) in [
        (
            "identity",
            "int128",
            "-170141183460469231731687303715884105728",
        ),
        (
            "identity",
            "int128",
            "170141183460469231731687303715884105727",
        ),
        (
            "unsigned_identity",
            "uint128",
            "340282366920938463463374607431768211455",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_CONTRACTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"wide.cpp\"; {ty} {name}({ty} value) {{ requires to_integer(value) == {value}; ensures to_integer(result) == 0; }}"
        );
        fs::write(project.directory.join("wide.click"), &source).unwrap();
        let parsed = read_click_project(&project.directory.join("wide.click"), &source).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("unclosed goal"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn wide_contracts_refuse_signedness_and_width_mismatches() {
    let project = Project::with_fixture("wide.cpp", "identity", WIDE_CONTRACTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    for signature in [
        "uint128 identity(int128 value)",
        "int64 identity(int128 value)",
        "int128 identity(uint128 value)",
        "int128 identity(int64 value)",
    ] {
        let proof = format!(
            "verifying \"wide.cpp\"; {signature} {{ ensures to_integer(result) == to_integer(result); }}"
        );
        let sidecar = project.directory.join("mismatch.click");
        fs::write(&sidecar, &proof).unwrap();
        let parsed = read_click_project(&sidecar, &proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("signature mismatch"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn wide_contracts_nested_calls_compose_observer_chains() {
    let project = Project::with_fixture("wide.cpp", "nested", WIDE_CONTRACTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "wide.cpp";
int128 identity(int128 value) { ensures to_integer(result) == to_integer(value); }
int128 nested(int128 value) { ensures to_integer(result) == to_integer(result); }
"#;
    check_selected_claim_certificate(&project, &import, proof);
    // The caller composes both identity contracts through the observer chain.
    let stronger = proof.replace(
        "int128 nested(int128 value) { ensures to_integer(result) == to_integer(result); }",
        "int128 nested(int128 value) { ensures to_integer(result) == to_integer(value); }",
    );
    check_selected_claim_certificate(&project, &import, &stronger);
    let false_result = stronger.replace(
        "int128 nested(int128 value) { ensures to_integer(result) == to_integer(value); }",
        "int128 nested(int128 value) { ensures to_integer(result) == to_integer(value) + 1; }",
    );
    assert_ne!(false_result, stronger);
    let sidecar = project.directory.join("nested.click");
    fs::write(&sidecar, &false_result).unwrap();
    let parsed = read_click_project(&sidecar, &false_result).unwrap();
    let error = match verify_program_prepared_project(&parsed, &import) {
        Err(error) => error,
        Ok(_) => panic!("composing identity calls must not prove an off-by-one result"),
    };
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn wide_contracts_parameter_preparation_scales_with_the_signature() {
    let mut samples = Vec::new();
    for size in [2usize, 8, 32, 128] {
        let params = (0..size)
            .map(|index| format!("__int128 p{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let source = format!("__int128 select({params}) noexcept {{ return p0; }}");
        let project = Project::with_fixture("wide.cpp", "select", &source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        assert_eq!(lowered.unwrap().kernel_function().parameters().len(), size);
        assert!(work <= 128 * size + 128, "{size}: {work}");
        samples.push((size, work));
        let params = (0..size)
            .map(|index| format!("int128 p{index}"))
            .collect::<Vec<_>>()
            .join(", ");
        let proof = format!(
            "verifying \"wide.cpp\"; int128 select({params}) {{ ensures to_integer(result) == to_integer(p0); }}"
        );
        check_arithmetic_sidecar(&project, &import, &proof);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0) + 128,
            "{samples:?}"
        );
    }
}

const WIDE_DIVISION_SOURCE: &str =
    include_str!("fixtures/cpp-verification/wide-division/division.cpp");
const WIDE_SIGNED_DOMAIN: &str = "requires to_integer(b) != 0; requires to_integer(a) != -170141183460469231731687303715884105728 or to_integer(b) != -1;";

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn wide_division_symbolic_contracts_verify_expand_and_audit_offline() {
    for (name, ty, helper, domain) in [
        (
            "signed_quotient",
            "int128",
            "truncating_quotient",
            WIDE_SIGNED_DOMAIN,
        ),
        (
            "signed_remainder",
            "int128",
            "truncating_remainder",
            WIDE_SIGNED_DOMAIN,
        ),
        (
            "unsigned_quotient",
            "uint128",
            "truncating_quotient",
            "requires to_integer(b) != 0;",
        ),
        (
            "unsigned_remainder",
            "uint128",
            "truncating_remainder",
            "requires to_integer(b) != 0;",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_DIVISION_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert_eq!(import.export().schema, 61);
        let source = format!(
            "verifying \"wide.cpp\"; {ty} {name}({ty} a, {ty} b) {{ {domain} ensures to_integer(result) == {helper}(to_integer(a), to_integer(b)); }}"
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace("requires to_integer(b) != 0;", "");
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
        if ty == "int128" {
            for endpoint in [
                "requires to_integer(a) == -170141183460469231731687303715884105728;",
                "requires to_integer(b) == -1;",
            ] {
                let specialized = source.replace(domain, &format!("{domain} {endpoint}"));
                check_selected_claim_certificate(&project, &import, &specialized);
            }
            let unsafe_source = source.replace("requires to_integer(a) != -170141183460469231731687303715884105728 or to_integer(b) != -1;", "");
            let path = project.directory.join("overflow.click");
            fs::write(&path, &unsafe_source).unwrap();
            let parsed = read_click_project(&path, &unsafe_source).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
        let false_source = source.replace(
            &format!("== {helper}(to_integer(a), to_integer(b))"),
            &format!("== {helper}(to_integer(a), to_integer(b)) + 1"),
        );
        let path = project.directory.join("false.click");
        fs::write(&path, &false_source).unwrap();
        let parsed = read_click_project(&path, &false_source).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn wide_division_full_width_constant_results_keep_all_bits() {
    for (name, ty, expected) in [
        ("constant_signed", "int128", "-1"),
        (
            "constant_unsigned",
            "uint128",
            "113427455640312821154458202477256070485",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_DIVISION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"wide.cpp\"; {ty} {name}() {{ ensures to_integer(result) == {expected}; }}"
        );
        check_first_claim_certificate(&project, &import, &source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn wide_division_modular_calls_frame_narrow_memory() {
    let project = Project::with_fixture("wide.cpp", "signed_relay", WIDE_DIVISION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = format!(
        r#"verifying "wide.cpp";
int128 signed_quotient(int128 a, int128 b) {{
    {WIDE_SIGNED_DOMAIN}
    ensures to_integer(result) == truncating_quotient(to_integer(a), to_integer(b));
}}
int128 signed_relay(int128 a, int128 b, int32* untouched) {{
    {WIDE_SIGNED_DOMAIN}
    owns untouched[0..1];
    ensures to_integer(result) == truncating_quotient(to_integer(a), to_integer(b));
    ensures untouched[0] == old(untouched[0]);
}}
"#
    );
    check_selected_claim_certificate(&project, &import, &source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn wide_division_preserves_clang_promotions_and_concrete_modulo_casts() {
    for (name, signed) in [("mixed_quotient", false), ("narrow_divisor", true)] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_DIVISION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [
            CppStatement::Return {
                value:
                    CppExpression::Binary {
                        left,
                        right,
                        value_type,
                        ..
                    },
                ..
            },
        ] = import.export().functions[0].body.as_slice()
        else {
            panic!("division must retain its explicit expression");
        };
        assert!(
            matches!(value_type, CppType::Integer { bits: 128, signed: value_signed, .. } if *value_signed == signed)
        );
        assert!(
            matches!(if signed { right.as_ref() } else { left.as_ref() }, CppExpression::IntegralCast { value_type: CppType::Integer { bits: 128, signed: value_signed, .. }, .. } if *value_signed == signed)
        );
        lower_import(&import).unwrap();
        if signed {
            let proof = format!(
                "verifying \"wide.cpp\"; int128 narrow_divisor(int128 a, int64 b) {{ {WIDE_SIGNED_DOMAIN} ensures to_integer(result) == truncating_quotient(to_integer(a), to_integer(b)); }}"
            );
            check_first_claim_certificate(&project, &import, &proof);
        }
    }
    let project = Project::with_fixture("wide.cpp", "mixed_constant", WIDE_DIVISION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_first_claim_certificate(
        &project,
        &import,
        "verifying \"wide.cpp\"; uint128 mixed_constant() { ensures to_integer(result) == 113427455640312821154458202477256070485; }",
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn wide_division_native_undefined_behavior_cannot_be_hidden_by_trivial_posts() {
    for (name, ty, domain, diagnostic) in [
        (
            "signed_quotient",
            "int128",
            "requires to_integer(b) == 0;",
            "division by zero",
        ),
        (
            "unsigned_remainder",
            "uint128",
            "requires to_integer(b) == 0;",
            "division by zero",
        ),
        (
            "signed_quotient",
            "int128",
            "requires to_integer(b) != 0; requires to_integer(a) == -170141183460469231731687303715884105728; requires to_integer(b) == -1;",
            "overflow",
        ),
        (
            "signed_remainder",
            "int128",
            "requires to_integer(b) != 0; requires to_integer(a) == -170141183460469231731687303715884105728; requires to_integer(b) == -1;",
            "overflow",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_DIVISION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof = format!(
            "verifying \"wide.cpp\"; {ty} {name}({ty} a, {ty} b) {{ {domain} ensures 0 == 0; }}"
        );
        let path = project.directory.join("unsafe.click");
        fs::write(&path, &proof).unwrap();
        let parsed = read_click_project(&path, &proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(error.message().contains(diagnostic), "{}", error.message());
    }
}

const WIDE_COMPARISONS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/wide-comparisons/comparisons.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn wide_comparisons_symbolic_results_verify_expand_and_audit_offline() {
    for (prefix, ty) in [("signed", "int128"), ("unsigned", "uint128")] {
        for (name, op) in [
            ("equal", "=="),
            ("not_equal", "!="),
            ("less", "<"),
            ("greater", ">"),
            ("less_equal", "<="),
            ("greater_equal", ">="),
        ] {
            let name = format!("{prefix}_{name}");
            let project = Project::with_fixture("wide.cpp", &name, WIDE_COMPARISONS_SOURCE);
            refresh_import(&project.config()).unwrap();
            fs::remove_file(&project.exporter).unwrap();
            let import = load_import(&project.config()).unwrap();
            assert_eq!(import.export().schema, 61);
            let relation = format!("to_integer(a) {op} to_integer(b)");
            let proof = format!(
                "verifying \"wide.cpp\"; bool {name}({ty} a, {ty} b) {{ ensures result == true implies ({relation}); ensures result == false implies not ({relation}); }}"
            );
            check_selected_claim_certificate(&project, &import, &proof);
            let false_proof = proof.replace(
                "ensures result == false implies not",
                "ensures result == false implies",
            );
            let path = project.directory.join("false.click");
            fs::write(&path, &false_proof).unwrap();
            let parsed = read_click_project(&path, &false_proof).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn wide_comparisons_constants_preserve_high_bits_signedness_and_promotions() {
    for (name, expected) in [
        ("high_equal_zero", false),
        ("minimum_negative", true),
        ("unsigned_max_positive", true),
        ("mixed_constant", true),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_COMPARISONS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof =
            format!("verifying \"wide.cpp\"; bool {name}() {{ ensures result == {expected}; }}");
        check_arithmetic_sidecar(&project, &import, &proof);
        let false_proof = proof.replace(&format!("== {expected}"), &format!("== {}", !expected));
        let path = project.directory.join("false.click");
        fs::write(&path, &false_proof).unwrap();
        let parsed = read_click_project(&path, &false_proof).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
    let project = Project::with_fixture("wide.cpp", "narrow_compare", WIDE_COMPARISONS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"wide.cpp\"; bool narrow_compare(int128 a, int64 b) { ensures result == true implies to_integer(a) < to_integer(b); ensures result == false implies not (to_integer(a) < to_integer(b)); }",
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn wide_comparisons_control_branches_and_frame_modular_call_memory() {
    let project = Project::with_fixture("wide.cpp", "choose", WIDE_COMPARISONS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"wide.cpp\"; int32 choose(int128 a, int128 b) { ensures to_integer(a) < to_integer(b) implies result == 7; ensures not (to_integer(a) < to_integer(b)) implies result == 11; }";
    check_first_claim_certificate(&project, &import, proof);
    let project = Project::with_fixture("wide.cpp", "relay", WIDE_COMPARISONS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "wide.cpp";
bool signed_less(int128 a, int128 b) {
    requires to_integer(a) < to_integer(b);
    ensures result == true;
}
bool relay(int128 a, int128 b, int32* untouched) {
    requires to_integer(a) < to_integer(b);
    owns untouched[0..1];
    ensures result == true;
    ensures untouched[0] == old(untouched[0]);
}
"#;
    check_selected_claim_certificate(&project, &import, proof);
}

#[test]
fn wide_comparisons_do_not_erase_operand_division_guards() {
    let project = Project::with_fixture("wide.cpp", "unsafe_operand", WIDE_COMPARISONS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    for domain in ["", "requires to_integer(b) != 0;"] {
        let proof = format!(
            "verifying \"wide.cpp\"; bool unsafe_operand(int128 a, int128 b) {{ {domain} ensures 0 == 0; }}"
        );
        let path = project.directory.join("unsafe.click");
        fs::write(&path, &proof).unwrap();
        let parsed = read_click_project(&path, &proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("undefined behavior"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn wide_comparisons_recognize_complementary_contract_premises() {
    for (name, inverse) in [
        ("equal", "!="),
        ("not_equal", "=="),
        ("less", ">="),
        ("less_equal", ">"),
        ("greater", "<="),
        ("greater_equal", "<"),
    ] {
        for (prefix, ty) in [("signed", "int128"), ("unsigned", "uint128")] {
            let name = format!("{prefix}_{name}");
            let project = Project::with_fixture("wide.cpp", &name, WIDE_COMPARISONS_SOURCE);
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let proof = format!(
                "verifying \"wide.cpp\"; bool {name}({ty} a, {ty} b) {{ requires to_integer(a) {inverse} to_integer(b); ensures result == false; }}"
            );
            check_arithmetic_sidecar(&project, &import, &proof);
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn not_equal_source_supports_the_existing_narrow_scalar_widths() {
    for (cpp, ty) in [
        ("int", "int32"),
        ("unsigned int", "uint32"),
        ("long", "int64"),
        ("unsigned long", "uint64"),
    ] {
        let source = format!("bool unequal({cpp} a, {cpp} b) noexcept {{ return a != b; }}");
        let project = Project::with_fixture("comparison.cpp", "unequal", &source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof = format!(
            "verifying \"comparison.cpp\"; bool unequal({ty} a, {ty} b) {{ ensures result == true implies a != b; ensures result == false implies a == b; }}"
        );
        check_arithmetic_sidecar(&project, &import, &proof);
    }
}

const WIDE_NARROWING_SOURCE: &str =
    include_str!("fixtures/cpp-verification/wide-narrowing/narrow.cpp");

fn cast_identity_proof(original: &str, lo: &str, hi: &str) -> String {
    format!(r#"close() using {{ {lo} <= {original}; {original} <= {hi}; }};"#)
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn wide_narrowing_preserves_symbolic_values_only_with_checked_destination_bounds() {
    for (name, source, result, lo, hi) in [
        (
            "ss64",
            "int128",
            "int64",
            "-9223372036854775808",
            "9223372036854775807",
        ),
        ("ss32", "int128", "int32", "-2147483648", "2147483647"),
        ("su64", "int128", "uint64", "0", "18446744073709551615"),
        ("su32", "int128", "uint32", "0", "4294967295"),
        ("us64", "uint128", "int64", "0", "9223372036854775807"),
        ("us32", "uint128", "int32", "0", "2147483647"),
        ("uu64", "uint128", "uint64", "0", "18446744073709551615"),
        ("uu32", "uint128", "uint32", "0", "4294967295"),
    ] {
        let project = Project::with_fixture("narrow.cpp", name, WIDE_NARROWING_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let cert = cast_identity_proof("to_integer(a)", lo, hi);
        let proof = format!(
            "verifying \"narrow.cpp\"; {result} {name}({source} a) {{ requires {lo} <= to_integer(a); requires to_integer(a) <= {hi}; ensures to_integer(result) == to_integer(a); }} by {{ step_until(function.exit); have to_integer(result) == to_integer(a) by {{ {cert} }} close(); }}"
        );
        check_selected_claim_certificate(&project, &import, &proof);
        for missing in [
            format!("requires {lo} <= to_integer(a);"),
            format!("requires to_integer(a) <= {hi};"),
        ] {
            let false_proof = proof.replace(&missing, "");
            let path = project.directory.join("missing.click");
            fs::write(&path, &false_proof).unwrap();
            let parsed = read_click_project(&path, &false_proof).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn wide_narrowing_quotient_and_remainder_keep_native_definedness_and_range_bounds() {
    for (name, result, op, lo, hi) in [
        (
            "quotient",
            "int64",
            "/",
            "-9223372036854775808",
            "9223372036854775807",
        ),
        ("remainder", "int32", "%", "-2147483648", "2147483647"),
    ] {
        let project = Project::with_fixture("narrow.cpp", name, WIDE_NARROWING_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let observed = format!("to_integer(a {op} b)");
        let cert = cast_identity_proof(&observed, lo, hi);
        let proof = format!(
            "verifying \"narrow.cpp\"; {result} {name}(int128 a, int128 b) {{ requires to_integer(b) != 0; requires to_integer(a) != -170141183460469231731687303715884105728 or to_integer(b) != -1; requires {lo} <= {observed}; requires {observed} <= {hi}; ensures to_integer(result) == {observed}; }} by {{ step_until(function.exit); have to_integer(result) == {observed} by {{ {cert} }} close(); }}"
        );
        check_first_claim_certificate(&project, &import, &proof);
        let unsafe_proof = format!(
            "verifying \"narrow.cpp\"; {result} {name}(int128 a, int128 b) {{ ensures 0 == 0; }}"
        );
        let path = project.directory.join("unsafe.click");
        fs::write(&path, &unsafe_proof).unwrap();
        let parsed = read_click_project(&path, &unsafe_proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("division by zero"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn wide_narrowing_still_wraps_outside_the_destination_range() {
    for (name, ty, expected) in [
        ("wrap_high", "int64", "0"),
        ("wrap_negative", "uint64", "18446744073709551615"),
        ("wrap_unsigned_max", "int64", "-1"),
    ] {
        let project = Project::with_fixture("narrow.cpp", name, WIDE_NARROWING_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof = format!(
            "verifying \"narrow.cpp\"; {ty} {name}() {{ ensures to_integer(result) == {expected}; }}"
        );
        check_first_claim_certificate(&project, &import, &proof);
        let false_proof = proof.replace(
            expected,
            if expected == "0" {
                "18446744073709551616"
            } else {
                "0"
            },
        );
        let path = project.directory.join("false.click");
        fs::write(&path, &false_proof).unwrap();
        let parsed = read_click_project(&path, &false_proof).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn wide_narrowing_modular_contract_preserves_framed_narrow_memory() {
    let project = Project::with_fixture("narrow.cpp", "relay", WIDE_NARROWING_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lo = "-9223372036854775808";
    let hi = "9223372036854775807";
    let cert = cast_identity_proof("to_integer(a)", lo, hi);
    let proof = format!(
        r#"verifying "narrow.cpp";
int64 ss64(int128 a) {{
    requires {lo} <= to_integer(a);
    requires to_integer(a) <= {hi};
    ensures to_integer(result) == to_integer(a);
}} by {{ step_until(function.exit); have to_integer(result) == to_integer(a) by {{ {cert} }} close(); }}
int64 relay(int128 a, int32* untouched) {{
    requires {lo} <= to_integer(a);
    requires to_integer(a) <= {hi};
    owns untouched[0..1];
    ensures to_integer(result) == to_integer(a);
    ensures untouched[0] == old(untouched[0]);
}}"#
    );
    check_selected_claim_certificate(&project, &import, &proof);
}

const SCALAR_BRACES_SOURCE: &str =
    include_str!("fixtures/cpp-verification/scalar-braces/braces.cpp");

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn scalar_brace_initialization_preserves_resolved_conversions_offline() {
    for (name, ty, params, post) in [
        ("signed32", "int32", "int32 n", "result == n"),
        ("signed64", "int64", "int64 n", "result == n"),
        ("unsigned32", "uint32", "uint32 n", "result == n"),
        ("unsigned64", "uint64", "uint64 n", "result == n"),
        (
            "signed128",
            "int128",
            "int128 n",
            "to_integer(result) == to_integer(n)",
        ),
        (
            "unsigned128",
            "uint128",
            "uint128 n",
            "to_integer(result) == to_integer(n)",
        ),
        ("widen", "int64", "int32 n", "result == n"),
        ("truth", "bool", "", "result == true"),
        ("constant", "int64", "", "result == 2147483648i64"),
    ] {
        let project = Project::with_fixture("braces.cpp", name, SCALAR_BRACES_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source =
            format!("verifying \"braces.cpp\"; {ty} {name}({params}) {{ ensures {post}; }}");
        check_first_claim_certificate(&project, &import, &source);
    }
}

#[test]
fn scalar_braces_do_not_convert_narrowing_or_unsupported_initializers_into_casts() {
    for (params, value) in [
        ("long n", "int{n}"),
        ("int n", "U32{n}"),
        ("int n", "bool{n}"),
        ("int n", "int{n, 1}"),
        ("int n", "int{}"),
        ("int n", "char{1}"),
        ("int n", "int{1.0}"),
        ("int n", "int{missing()}"),
        ("int n", "int{++n}"),
    ] {
        let cpp = format!(
            "using U32 = unsigned; int missing(); int refused({params}) noexcept {{ return {value}; }}"
        );
        let project = Project::with_fixture("braces.cpp", "refused", &cpp);
        refresh_import(&project.config())
            .expect_err("unsupported initialization must remain refused");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn scalar_braces_compose_verified_fee_products_and_frame_memory() {
    let project = Project::with_fixture("braces.cpp", "relay", SCALAR_BRACES_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let helper = include_str!("../integrations/bitcoin-core-money-range/FeeFracMul.click")
        .replace("bitcoin-src/src/util/feefrac.h", "braces.cpp");
    let source = format!(
        r#"{helper}
int128 relay(int64 a, int32 b, int32& untouched) {{
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires -2147483648 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    owns untouched;
    ensures to_integer(result) == to_integer(a) * to_integer(b);
    ensures untouched == old(untouched);
}}
"#
    );
    check_selected_claim_certificate(&project, &import, &source);
    let hostile = source.replace(
        "ensures to_integer(result) == to_integer(a) * to_integer(b);",
        "ensures to_integer(result) == to_integer(a) * to_integer(b) + 1;",
    );
    let path = project.directory.join("false.click");
    fs::write(&path, &hostile).unwrap();
    let parsed = read_click_project(&path, &hostile).unwrap();
    verify_program_prepared_project(&parsed, &import).expect_err("false product claims must fail");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn scalar_braces_keep_argument_and_assumption_effect_restrictions() {
    let project = Project::with_fixture("braces.cpp", "argument", SCALAR_BRACES_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"braces.cpp\"; int64 identity(int64 n) { ensures result == n; } int64 argument(int32 n) { ensures result == n; }";
    check_selected_claim_certificate(&project, &import, proof);
    let project = Project::with_fixture("braces.cpp", "guarded", SCALAR_BRACES_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof =
        "verifying \"braces.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; }";
    check_first_claim_certificate(&project, &import, proof);
    let path = project.directory.join("missing.click");
    let missing = proof.replace("requires n > 0;", "");
    fs::write(&path, &missing).unwrap();
    let parsed = read_click_project(&path, &missing).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .expect_err("braces cannot discharge an assumption");
    for cpp in [
        "long identity(long n) noexcept { return n; } long argument(int n) noexcept { return identity(long{++n}); }",
        "int guarded(int n) noexcept { __builtin_assume(bool{++n > 0}); return n; }",
        "int guarded(int n) noexcept { __builtin_assume(bool{n + 1 > 0}); return n; }",
    ] {
        let name = if cpp.starts_with("long") {
            "argument"
        } else {
            "guarded"
        };
        let project = Project::with_fixture("braces.cpp", name, cpp);
        refresh_import(&project.config())
            .expect_err("braces must not hide effects or partial arithmetic");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

fn library_assertion_fixture(header: &str, cpp: &str) -> Project {
    use sha2::{Digest, Sha256};
    let mut project = Project::with_fixture("library.cpp", "guarded", cpp);
    fs::write(project.directory.join("gate.h"), header).unwrap();
    project.dependencies.push("gate.h".into());
    project.write_config("guarded");
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["library_assertions"] = serde_json::json!([{
        "kind": "checked_boolean_statement",
        "function": "library::check",
        "header": "gate.h",
        "sha256": format!("{:x}", Sha256::digest(header.as_bytes()))
    }]);
    fs::write(
        project.config(),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();
    project
}

const LIBRARY_ASSERTION_HEADER: &str = "namespace library { inline bool check(bool value) noexcept { if (!value) __builtin_trap(); return value; } }\n#define Gate(value) library::check(value)\n";

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn assumed_library_assertions_require_proof_and_preserve_cleanup() {
    let cpp = "#include \"gate.h\"\nstruct Guard { int value; explicit Guard(int n) noexcept : value(n) {} ~Guard() noexcept { value = 0; } };\nint guarded(int n) noexcept { Guard guard(n); Gate(n > 0); return n; }";
    let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, cpp);
    refresh_import(&project.config()).unwrap();
    let artifact = fs::read(project.artifact()).unwrap();
    refresh_import(&project.config()).unwrap();
    assert_eq!(artifact, fs::read(project.artifact()).unwrap());
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(
        import
            .export()
            .reachable_functions
            .iter()
            .all(|f| f.name != "library_check")
    );
    let CppStatement::LibraryAssert { contract, span, .. } = &import.export().functions[0].body[1]
    else {
        panic!("explicit library assertion node")
    };
    assert_eq!(contract.function, "library::check");
    assert_eq!(contract.header, "gate.h");
    assert_eq!(span.file, "library.cpp");
    let source = r#"verifying "library.cpp";
Guard::Guard(int32 n) { owns this->value; ensures this->value == n; }
Guard::~Guard() { owns this->value; ensures this->value == 0; }
int32 guarded(int32 n) { requires n > 0; ensures result == n; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    for precondition in ["", "requires n == 0;"] {
        let hostile = source.replace("requires n > 0;", precondition);
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error
                .message()
                .contains("assumed library contract `library::check`"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains(&contract.sha256),
            "{}",
            error.message()
        );
    }
    let hostile = source.replace("ensures result == n;", "ensures result == n + 1;");
    let path = project.directory.join("false.click");
    fs::write(&path, &hostile).unwrap();
    let parsed = read_click_project(&path, &hostile).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .expect_err("a proved library condition cannot prove a false return");
    fs::write(
        project.directory.join("gate.h"),
        format!("{LIBRARY_ASSERTION_HEADER}\n// changed\n"),
    )
    .unwrap();
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("explicit pin")
    );
}

#[test]
fn assumed_library_assertions_reject_unpinned_and_effectful_boundaries() {
    let cpp =
        "#include \"gate.h\"\nint guarded(int n) noexcept { library::check(n > 0); return n; }";
    for (header, body) in [
        (LIBRARY_ASSERTION_HEADER, cpp.replace("n > 0", "++n > 0")),
        (LIBRARY_ASSERTION_HEADER, cpp.replace("n > 0", "n + 1 > 0")),
        (
            "namespace library { void check(bool, int); }",
            cpp.replace("n > 0", "n > 0, ++n"),
        ),
        ("namespace library { void check(int); }", cpp.to_string()),
        (
            "namespace library { void check(bool&); }",
            "#include \"gate.h\"\nint guarded(bool n) noexcept { library::check(n); return 0; }"
                .to_string(),
        ),
        ("namespace library { int check(bool); }", cpp.to_string()),
        (
            "namespace library { template<class T> void check(T); }",
            cpp.to_string(),
        ),
        (
            LIBRARY_ASSERTION_HEADER,
            cpp.replace(
                "library::check(n > 0); return n;",
                "return library::check(n > 0);",
            ),
        ),
    ] {
        let project = library_assertion_fixture(header, &body);
        refresh_import(&project.config())
            .expect_err("unsupported argument/signature/use must fail atomically");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
    let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, cpp);
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["library_assertions"] = serde_json::json!([]);
    fs::write(project.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&project.config())
        .expect_err("external assertion calls need an explicit contract");
    assert!(!project.artifact().exists());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn evaluated_library_assertions_read_fields_with_normal_authority() {
    let cpp = "#include \"gate.h\"\nstruct Box { int size; }; int guarded(const Box& box, int n) noexcept { Gate(box.size > 0 && n >= 0); return n; }";
    let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "library.cpp";
int32 guarded(const struct Box& box, int32 n) {
 views box.size;
 requires box.size > 0;
 requires n >= 0;
 ensures result == n;
 ensures box.size == old(box.size);
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    for bad in [
        proof.replace("views box.size;", ""),
        proof.replace("requires box.size > 0;", ""),
        proof.replace("requires n >= 0;", ""),
        proof.replace("ensures result == n;", "ensures result != n;"),
    ] {
        let path = project.directory.join("hostile.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn library_field_conditions_keep_builtin_and_effect_boundaries() {
    for cpp in [
        "#include \"gate.h\"\nstruct Box { int size; }; int guarded(const Box& box) noexcept { __builtin_assume(box.size > 0); return 0; }",
        "#include \"gate.h\"\nstruct Box { int size; }; int guarded(const Box& box) noexcept { Gate(box.size + 1 > 0); return 0; }",
        "#include \"gate.h\"\nstruct Box { int size; }; int guarded(Box& box) noexcept { Gate(++box.size > 0); return 0; }",
        "#include \"gate.h\"\nstruct Box { volatile int size; }; int guarded(const Box& box) noexcept { Gate(box.size > 0); return 0; }",
        "#include \"gate.h\"\nint guarded(const int* value) noexcept { Gate(*value > 0); return 0; }",
    ] {
        let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, cpp);
        refresh_import(&project.config())
            .expect_err("field admission must preserve effect/totality restrictions");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn evaluated_field_assertions_scale_with_selected_statements() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let body = "Gate(box.size > 0);\n".repeat(size);
        let cpp = format!(
            "#include \"gate.h\"\nstruct Box {{ int size; }}; int guarded(const Box& box) noexcept {{ {body} return 0; }}"
        );
        let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, &cpp);
        refresh_import(&project.config()).unwrap();
        let (loaded, validation_work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = loaded.unwrap();
        let (lowered, lowering_work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        samples.push((validation_work, lowering_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 6 && pair[1].1 <= pair[0].1 * 6,
            "{samples:?}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn branch_likelihood_attributes_preserve_both_outcomes() {
    let cpp = "int choose(bool positive) noexcept { if (positive) [[likely]] { return 7; } else [[unlikely]] { return -3; } }";
    let project = Project::with_fixture("weights.cpp", "choose", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "weights.cpp";
int32 choose(bool positive) {
 ensures positive == true implies result == 7;
 ensures positive == false implies result == -3;
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let bad = proof.replace("result == 7", "result == 8");
    let path = project.directory.join("bad.click");
    fs::write(&path, &bad).unwrap();
    let parsed = read_click_project(&path, &bad).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
    let project = Project::with_fixture(
        "weights.cpp",
        "caller",
        "int callee(int n) noexcept { return n; } int caller(int n) noexcept { [[clang::musttail]] return callee(n); }",
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("only likely/unlikely"), "{error}");
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

#[test]
fn assumed_library_assertion_inventory_and_pins_are_checked_before_export() {
    let cpp =
        "#include \"gate.h\"\nint guarded(int n) noexcept { library::check(n > 0); return n; }";
    for change in [
        "hash",
        "header",
        "function",
        "kind",
        "duplicate",
        "too_many",
    ] {
        let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, cpp);
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
        match change {
            "hash" => config["library_assertions"][0]["sha256"] = "0".repeat(64).into(),
            "header" => config["library_assertions"][0]["header"] = "../gate.h".into(),
            "function" => config["library_assertions"][0]["function"] = "check()".into(),
            "kind" => config["library_assertions"][0]["kind"] = "unchecked_assumption".into(),
            "duplicate" => {
                let duplicate = config["library_assertions"][0].clone();
                config["library_assertions"]
                    .as_array_mut()
                    .unwrap()
                    .push(duplicate);
            }
            "too_many" => {
                config["library_assertions"] =
                    serde_json::Value::Array(vec![config["library_assertions"][0].clone(); 65])
            }
            _ => unreachable!(),
        }
        fs::write(project.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        if change != "hash" {
            fs::remove_file(&project.exporter).unwrap();
        }
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            !error.contains("resolve C++ exporter"),
            "policy must be checked before invoking Clang: {error}"
        );
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn assumed_library_assertions_bind_offline_artifacts_to_config_authority() {
    use sha2::{Digest, Sha256};
    let cpp = "#include \"gate.h\"\nint checked(int n) noexcept { library::check(n > 0); return n; }\nint guarded(int n) noexcept { return checked(n); }";
    for change in [
        "function",
        "hash",
        "header",
        "invalid_hash",
        "remove_authority",
    ] {
        let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let mut artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        assert_eq!(
            artifact["reachable_functions"][0]["body"][0]["kind"],
            "library_assert"
        );
        let contract = &mut artifact["reachable_functions"][0]["body"][0]["contract"];
        let mut lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        match change {
            "function" => contract["function"] = "library::other".into(),
            "hash" => contract["sha256"] = "0".repeat(64).into(),
            "header" => contract["header"] = "other.h".into(),
            "invalid_hash" => contract["sha256"] = "F".repeat(64).into(),
            "remove_authority" => {
                let mut config: serde_json::Value =
                    serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
                config["library_assertions"] = serde_json::json!([]);
                fs::write(project.config(), serde_json::to_vec(&config).unwrap()).unwrap();
                unit_entry_mut(&mut lock)["unit"] = unit_digest(&project.config()).into();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(
            error.contains("library assertion") || error.contains("library assertion contract"),
            "semantic authority must be checked even with updated file digests: {error}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn assumed_library_assertions_scale_with_explicit_statement_count() {
    for size in [4usize, 16, 64, 256] {
        let body = "library::check(n > 0);\n".repeat(size);
        let cpp =
            format!("#include \"gate.h\"\nint guarded(int n) noexcept {{ {body} return n; }}");
        let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = project.loaded_artifact_bytes();
        let (import, work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert!(
            work <= bytes + 64 * size + 256,
            "{size}: {work} for {bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(work <= 32 * size + 128, "{size}: {work}");
        if size == 4 {
            let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; }";
            check_selected_claim_certificate(&project, &import, proof);
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn assumed_library_assertions_compose_with_modular_callers_and_memory_framing() {
    let cpp = "#include \"gate.h\"\nint checked(int n) noexcept { library::check(n > 0); return n; }\nint guarded(int& memory, int n) noexcept { return checked(n); }";
    // A declaration-only, void-return library boundary is also explicitly assumed.
    let project = library_assertion_fixture("namespace library { void check(bool); }", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "library.cpp";
int32 checked(int32 n) { requires n > 0; ensures result == n; }
int32 guarded(int32& memory, int32 n) { owns memory; requires memory == 7; requires n > 0; ensures memory == 7; ensures result == n; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    for hostile in [
        source.replacen("requires n > 0;", "", 1),
        source.replace("ensures memory == 7;", "ensures memory == 8;"),
    ] {
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect_err("library and modular contracts must preserve their obligations");
    }
}

#[test]
fn assumed_library_assertions_reject_matching_names_from_another_header() {
    let header = "#include \"other.h\"\n";
    let cpp =
        "#include \"gate.h\"\nint guarded(int n) noexcept { library::check(n > 0); return n; }";
    let project = library_assertion_fixture(header, cpp);
    fs::write(
        project.directory.join("other.h"),
        "namespace library { void check(bool); }",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("declaration differs from its pinned header"),
        "{error}"
    );
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

#[test]
fn assumed_library_assertions_cannot_bypass_selected_source_verification() {
    use sha2::{Digest, Sha256};
    let cpp = "namespace library { void check(bool value) noexcept { check(value); } }\nint guarded(int n) noexcept { library::check(n > 0); return n; }";
    let project = library_assertion_fixture("", cpp);
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["dependencies"] = serde_json::json!(["library.cpp"]);
    config["library_assertions"][0]["header"] = "library.cpp".into();
    config["library_assertions"][0]["sha256"] =
        format!("{:x}", Sha256::digest(cpp.as_bytes())).into();
    fs::write(project.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("selected-source C++ definitions require ordinary verified contracts"),
        "{error}"
    );
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

fn consteval_library_fixture(header: &str, cpp: &str) -> Project {
    let project = library_assertion_fixture(header, cpp);
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["library_assertions"][0]["kind"] =
        "checked_boolean_statement_with_consteval_metadata".into();
    fs::write(project.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    project
}

const CONSTEVAL_LIBRARY_HEADER: &str = r#"
namespace library {
struct Location { int line; };
consteval Location location() { return {3}; }
consteval int number() { return 7; }
template<bool Debug, class T> constexpr T&& check(T&& condition, const Location&, int) {
    if (Debug && !condition) __builtin_trap();
    return static_cast<T&&>(condition);
}
}
#define Gate(value) library::check<false>(value, library::location(), library::number())
"#;

#[test]
fn consteval_library_metadata_keeps_proof_obligations_and_compiler_origin() {
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let CppStatement::LibraryAssert {
        metadata,
        specialization,
        ..
    } = &import.export().functions[0].body[0]
    else {
        panic!("explicit library statement")
    };
    assert_eq!(metadata.len(), 2);
    let click::languages::cpp::CppLibraryMetadata::Consteval(location) = &metadata[0] else {
        panic!("consteval location")
    };
    let click::languages::cpp::CppLibraryMetadata::Consteval(number) = &metadata[1] else {
        panic!("consteval number")
    };
    assert_eq!(location.function, "library::location");
    assert_eq!(number.function, "library::number");
    assert_eq!(
        location.declaration_file,
        project
            .directory
            .join("gate.h")
            .canonicalize()
            .unwrap()
            .to_str()
            .unwrap()
    );
    assert_eq!(
        specialization.as_deref(),
        Some("library_check__bool_false__bool")
    );
    assert!(
        import.export().records.is_empty(),
        "compile-time-only opaque metadata does not become a runtime record model"
    );
    assert!(import.export().reachable_functions.is_empty());
    let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; }";
    check_selected_claim_certificate(&project, &import, proof);
    for hostile in [
        proof.replace("requires n > 0;", ""),
        proof.replace("requires n > 0;", "requires n == 0;"),
        proof.replace("ensures result == n;", "ensures result == n + 1;"),
    ] {
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .expect_err("metadata and templates cannot grant unproved conditions or false results");
    }
}

#[test]
fn consteval_library_metadata_rejects_runtime_calls_conversions_and_cleanup() {
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    for (header, body) in [
        (
            CONSTEVAL_LIBRARY_HEADER.replace("consteval Location", "constexpr Location"),
            cpp.to_string(),
        ),
        (
            CONSTEVAL_LIBRARY_HEADER.replace("consteval int", "constexpr int"),
            cpp.to_string(),
        ),
        (
            CONSTEVAL_LIBRARY_HEADER.replace(
                "struct Location { int line; };",
                "struct Location { int line; constexpr ~Location() {} };",
            ),
            cpp.to_string(),
        ),
        (
            CONSTEVAL_LIBRARY_HEADER.replace("const Location&", "Location"),
            cpp.to_string(),
        ),
        (
            CONSTEVAL_LIBRARY_HEADER.to_string(),
            cpp.replace("n > 0", "++n > 0"),
        ),
        (
            CONSTEVAL_LIBRARY_HEADER.to_string(),
            cpp.replace("n > 0", "n + 1 > 0"),
        ),
        (
            CONSTEVAL_LIBRARY_HEADER.to_string(),
            cpp.replace("Gate(n > 0); return n;", "return Gate(n > 0);"),
        ),
        (
            CONSTEVAL_LIBRARY_HEADER.to_string(),
            cpp.replace(
                "Gate(n > 0)",
                "library::check<false>(n > 0, library::location(), ++n)",
            ),
        ),
    ] {
        let project = consteval_library_fixture(&header, &body);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "bounded diagnostic");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn consteval_library_metadata_preserves_normal_cleanup_and_modular_framing() {
    let cpp = "#include \"gate.h\"\nstruct Guard { int value; explicit Guard(int n) noexcept : value(n) {} ~Guard() noexcept { value = 0; } };\nint checked(int n) noexcept { Gate(n > 0); return n; }\nint guarded(int& memory, int n) noexcept { Guard guard(n); return checked(n); }";
    let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "library.cpp";
Guard::Guard(int32 n) { owns this->value; ensures this->value == n; }
Guard::~Guard() { owns this->value; ensures this->value == 0; }
int32 checked(int32 n) { requires n > 0; ensures result == n; }
int32 guarded(int32& memory, int32 n) { owns memory; requires memory == 7; requires n > 0; ensures memory == 7; ensures result == n; }
"#;
    check_selected_claim_certificate(&project, &import, proof);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn consteval_library_metadata_offline_checker_rejects_forged_origin_and_kind() {
    use sha2::{Digest, Sha256};
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    for change in ["file", "function", "specialization", "too_many", "kind"] {
        let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, cpp);
        refresh_import(&project.config()).unwrap();
        let mut artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let statement = &mut artifact["functions"][0]["body"][0];
        match change {
            "file" => statement["metadata"][0]["declaration_file"] = "/outside/closure.h".into(),
            "function" => statement["metadata"][0]["function"] = "factory()".into(),
            "specialization" => statement["specialization"] = "check<false>".into(),
            "too_many" => {
                statement["metadata"] =
                    serde_json::Value::Array(vec![statement["metadata"][0].clone(); 9])
            }
            "kind" => statement["contract"]["kind"] = "checked_boolean_statement".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.contains("metadata"), "{error}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn consteval_library_metadata_scales_with_explicit_statement_count() {
    for size in [4usize, 16, 64, 256] {
        let body = "Gate(n > 0);\n".repeat(size);
        let cpp =
            format!("#include \"gate.h\"\nint guarded(int n) noexcept {{ {body} return n; }}");
        let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = project.loaded_artifact_bytes();
        let (import, work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert!(
            work <= bytes + 64 * size + 256,
            "{size}: {work} for {bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(work <= 32 * size + 128, "{size}: {work}");
    }
}

const LITERAL_TEXT_HEADER: &str = "namespace library { struct Text { const char* pointer; Text(const char* value) noexcept : pointer(value) {} }; }\n";
const LITERAL_LIBRARY_HEADER: &str = r#"
#include "text.h"
namespace library {
struct Location { int line; };
consteval Location location() { return {3}; }
template<bool Debug, class T> T&& check(T&& condition, const Location&, Text) {
    if (Debug && !condition) __builtin_trap();
    return static_cast<T&&>(condition);
}
}
#define Gate(value) library::check<false>(value, library::location(), #value)
"#;

fn literal_library_fixture(text: &str, header: &str, cpp: &str) -> Project {
    use sha2::{Digest, Sha256};
    let project = consteval_library_fixture(header, cpp);
    fs::write(project.directory.join("text.h"), text).unwrap();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["dependencies"] = serde_json::json!(["gate.h", "text.h"]);
    config["library_assertions"][0]["kind"] =
        "checked_boolean_statement_with_literal_metadata".into();
    config["library_assertions"][0]["literal_constructor"] = serde_json::json!({
        "function": "library::Text::Text", "header": "text.h",
        "sha256": format!("{:x}", Sha256::digest(text.as_bytes()))
    });
    fs::write(project.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    project
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn literal_library_metadata_proves_conditions_and_retains_both_assumptions() {
    use click::languages::cpp::{CppLibraryMetadata, CppLiteralMetadataBinding};
    for (header, binding) in [
        (
            LITERAL_LIBRARY_HEADER.to_string(),
            CppLiteralMetadataBinding::Value,
        ),
        (
            LITERAL_LIBRARY_HEADER.replace("&, Text)", "&, const Text&)"),
            CppLiteralMetadataBinding::ConstReference,
        ),
    ] {
        let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
        let project = literal_library_fixture(LITERAL_TEXT_HEADER, &header, cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let CppStatement::LibraryAssert {
            metadata, contract, ..
        } = &import.export().functions[0].body[0]
        else {
            panic!("library statement")
        };
        assert!(matches!(metadata[0], CppLibraryMetadata::Consteval(_)));
        let CppLibraryMetadata::Literal(literal) = &metadata[1] else {
            panic!("literal metadata")
        };
        assert_eq!(literal.literal, "n > 0");
        assert_eq!(literal.record, "library::Text");
        assert_eq!(literal.binding, binding);
        assert_eq!(
            Some(&literal.constructor),
            contract.literal_constructor.as_ref()
        );
        assert_eq!(
            literal.declaration_file,
            project
                .directory
                .join("text.h")
                .canonicalize()
                .unwrap()
                .to_str()
                .unwrap()
        );
        assert!(import.export().records.is_empty());
        assert!(import.export().reachable_functions.is_empty());
        let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; }";
        check_return_call_sidecar(&project, &import, proof);
        for hostile in [
            proof.replace("requires n > 0;", ""),
            proof.replace("requires n > 0;", "requires n == 0;"),
            proof.replace("ensures result == n;", "ensures result == n + 1;"),
        ] {
            let path = project.directory.join("hostile.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            if !hostile.contains("n + 1") {
                assert!(
                    error.message().contains("literal constructor"),
                    "{}",
                    error.message()
                );
            }
        }
    }
}

#[test]
fn literal_library_metadata_rejects_runtime_arguments_and_nontrivial_lifetimes() {
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    for (text, body) in [
        (LITERAL_TEXT_HEADER.replace("};", "~Text() {} };"), cpp.to_string()),
        (LITERAL_TEXT_HEADER.replace("};", "Text(const Text& other) : pointer(other.pointer) {} };"), cpp.to_string()),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("int n)", "int n, const char* message)").replace("Gate(n > 0)", "library::check<false>(n > 0, library::location(), message)")),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("Gate(n > 0)", "library::check<false>(n > 0, library::location(), static_cast<const char*>(nullptr))")),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("Gate(n > 0)", "library::check<false>(n > 0, library::location(), \"a\\0b\")")),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("Gate(n > 0)", "library::check<false>(n > 0, library::location(), \"é\")")),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("Gate(n > 0)", "Gate(++n > 0)")),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("Gate(n > 0); return n;", "return Gate(n > 0);")),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("Gate(n > 0)", "library::check<false>(n > 0, library::location(), (n++, \"message\"))")),
        (LITERAL_TEXT_HEADER.to_string(), cpp.replace("Gate(n > 0)", &format!("library::check<false>(n > 0, library::location(), \"{}\")", "a".repeat(4097)))),
    ] {
        let project = literal_library_fixture(&text, LITERAL_LIBRARY_HEADER, &body);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "bounded rejection");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
fn literal_library_metadata_requires_explicit_constructor_authority() {
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    for change in [
        "kind",
        "missing",
        "hash",
        "function",
        "header",
        "dependency",
    ] {
        let project = literal_library_fixture(LITERAL_TEXT_HEADER, LITERAL_LIBRARY_HEADER, cpp);
        let mut config: serde_json::Value =
            serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
        match change {
            "kind" => {
                config["library_assertions"][0]["kind"] =
                    "checked_boolean_statement_with_consteval_metadata".into()
            }
            "missing" => {
                config["library_assertions"][0]
                    .as_object_mut()
                    .unwrap()
                    .remove("literal_constructor");
            }
            "hash" => {
                config["library_assertions"][0]["literal_constructor"]["sha256"] =
                    "0".repeat(64).into()
            }
            "function" => {
                config["library_assertions"][0]["literal_constructor"]["function"] =
                    "library::Other::Other".into()
            }
            "header" => {
                config["library_assertions"][0]["literal_constructor"]["header"] = "gate.h".into();
                config["library_assertions"][0]["literal_constructor"]["sha256"] =
                    config["library_assertions"][0]["sha256"].clone();
            }
            "dependency" => config["dependencies"] = serde_json::json!(["gate.h"]),
            _ => unreachable!(),
        }
        fs::write(project.config(), serde_json::to_vec(&config).unwrap()).unwrap();
        refresh_import(&project.config()).unwrap_err();
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn literal_library_metadata_offline_checker_rejects_forged_constructor_and_literal() {
    use sha2::{Digest, Sha256};
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    for change in [
        "header", "hash", "file", "record", "literal", "binding", "kind",
    ] {
        let project = literal_library_fixture(LITERAL_TEXT_HEADER, LITERAL_LIBRARY_HEADER, cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let mut artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let literal = &mut artifact["functions"][0]["body"][0]["metadata"][1];
        match change {
            "header" => literal["constructor"]["header"] = "gate.h".into(),
            "hash" => literal["constructor"]["sha256"] = "0".repeat(64).into(),
            "file" => {
                literal["declaration_file"] = project
                    .directory
                    .join("gate.h")
                    .canonicalize()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .into()
            }
            "record" => literal["record"] = "library::Other".into(),
            "literal" => literal["literal"] = "a\0b".into(),
            "binding" => literal["binding"] = "mutable_reference".into(),
            "kind" => literal["kind"] = "consteval".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(
            error.contains("metadata") || error.contains("semantic artifact"),
            "{error}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn literal_library_metadata_scales_with_explicit_statement_count() {
    for size in [4usize, 16, 64, 256] {
        let cpp = format!(
            "#include \"gate.h\"\nint guarded(int n) noexcept {{ {} return n; }}",
            "Gate(n > 0);\n".repeat(size)
        );
        let project = literal_library_fixture(LITERAL_TEXT_HEADER, LITERAL_LIBRARY_HEADER, &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = project.loaded_artifact_bytes();
        let (import, work) =
            click::instrumentation::measure_deterministic_work(|| load_import(&project.config()));
        let import = import.unwrap();
        assert!(
            work <= bytes + 64 * size + 256,
            "{size}: {work} for {bytes} bytes"
        );
        let (lowered, work) =
            click::instrumentation::measure_deterministic_work(|| lower_import(&import));
        lowered.unwrap();
        assert!(work <= 32 * size + 128, "{size}: {work}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn literal_library_metadata_preserves_cleanup_and_modular_memory_framing() {
    let cpp = r#"#include "gate.h"
struct Guard { int value; explicit Guard(int n) noexcept : value(n) {} ~Guard() noexcept { value = 0; } };
int checked(int n) noexcept { Guard guard(n); Gate(n > 0); return n; }
int guarded(int& value, int* untouched) noexcept { int n = value; int result = checked(n); value = result; return result; }
"#;
    let project = literal_library_fixture(LITERAL_TEXT_HEADER, LITERAL_LIBRARY_HEADER, cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "library.cpp";
Guard::Guard(int32 n) { owns this->value; ensures this->value == n; }
Guard::~Guard() { owns this->value; ensures this->value == 0; }
int32 checked(int32 n) { requires n > 0; ensures result == n; }
int32 guarded(int32& value, int32* untouched) {
    owns value; owns untouched[0..1]; requires value > 0; requires untouched[0] == 7;
    ensures result == old(value); ensures value == old(value); ensures untouched[0] == 7;
}
"#;
    check_selected_claim_certificate(&project, &import, proof);
}

#[test]
fn literal_library_metadata_const_reference_does_not_execute_a_nontrivial_copy() {
    let text = LITERAL_TEXT_HEADER.replace(
        "};",
        "Text(const Text& other) : pointer(other.pointer) { __builtin_trap(); } };",
    );
    let header = LITERAL_LIBRARY_HEADER.replace("&, Text)", "&, const Text&)");
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    let project = literal_library_fixture(&text, &header, cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; }";
    check_selected_claim_certificate(&project, &import, proof);
    fs::write(
        project.directory.join("text.h"),
        format!("{text}\n// changed pin\n"),
    )
    .unwrap();
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("explicit pin")
    );
}

#[test]
fn literal_library_metadata_cannot_bypass_selected_source_constructor_verification() {
    let text = "namespace library { struct Text { const char* pointer; Text(const char* value) noexcept; }; }\n";
    let cpp = "#include \"gate.h\"\nlibrary::Text::Text(const char* value) noexcept : pointer(value) {}\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    let project = literal_library_fixture(text, LITERAL_LIBRARY_HEADER, cpp);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("pinned external header"), "{error}");
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn wide_division_operand_bounds_certify_native_narrowing() {
    for (name, ty, op, pure, lo, hi) in [
        (
            "quotient",
            "int64",
            "/",
            "truncating_quotient",
            "-9223372036854775808",
            "9223372036854775807",
        ),
        (
            "remainder",
            "int32",
            "%",
            "truncating_remainder",
            "-2147483648",
            "2147483647",
        ),
    ] {
        let project = Project::with_fixture("narrow.cpp", name, WIDE_NARROWING_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let certificate = |_goal: &str| {
            r#"close() using { -9223372036854775808 <= to_integer(a); to_integer(a) <= 9223372036854775807; 1 <= to_integer(b); to_integer(b) <= 2147483647; };"#.to_owned()
        };
        let expression = format!("{pure}(to_integer(a), to_integer(b))");
        let observed = format!("to_integer(a {op} b)");
        let lower = format!("{lo} <= {expression}");
        let upper = format!("{expression} <= {hi}");
        let lower_cert = certificate(&lower);
        let upper_cert = certificate(&upper);
        let cast_cert = cast_identity_proof(&observed, lo, hi);
        let proof = format!(
            r#"verifying "narrow.cpp";
{ty} {name}(int128 a, int128 b) {{
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires 1 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    requires to_integer(b) != 0;
    requires to_integer(b) != -1;
    ensures to_integer(result) == {expression};
}} by {{
    have {lower} by {{ {lower_cert} }}
    have {upper} by {{ {upper_cert} }}
    step_until(function.exit);
    have {lo} <= {observed} by {{ close() using {{ {observed} == {expression}; {lower}; }}; }}
    have {observed} <= {hi} by {{ close() using {{ {observed} == {expression}; {upper}; }}; }}
    have to_integer(result) == {observed} by {{ {cast_cert} }}
    have to_integer(result) == {expression} by {{ close() using {{ {observed} == {expression}; to_integer(result) == {observed}; }}; }}
    close();
}}
"#
        );
        check_arithmetic_sidecar(&project, &import, &proof);
        // `1 <= b` already excludes zero, so removing only `b != 0`
        // is not a negative control.
        for hostile in [
            proof.replace(
                "ensures to_integer(result) ==",
                "ensures to_integer(result) !=",
            ),
            proof.replace("    requires to_integer(a) <= 9223372036854775807;", ""),
            proof.replace("    requires 1 <= to_integer(b);", ""),
        ] {
            let path = project.directory.join("false.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import)
                .expect_err("false results and missing guards or bounds must fail");
            assert!(error.message().len() < 8000, "bounded refusal");
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn positive_integer_divisor_bounds_discharge_native_wide_guards() {
    for name in ["signed_quotient", "signed_remainder"] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_DIVISION_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            r#"verifying "wide.cpp";
int128 {name}(int128 a, int128 b) {{
    requires 1 <= to_integer(b);
    ensures 0 == 0;
}} by {{
    have to_integer(b) != 0 by {{ close() using {{ 1 <= to_integer(b); }}; }}
    have to_integer(b) != -1 by {{ close() using {{ 1 <= to_integer(b); }}; }}
    step_until(function.exit); close();
}}"#
        );
        check_first_claim_certificate(&project, &import, &source);
        for hostile in [
            source.replace("requires 1 <= to_integer(b);", ""),
            source.replace(
                "requires 1 <= to_integer(b);",
                "requires 0 <= to_integer(b);",
            ),
            source.replace("ensures 0 == 0;", "ensures 0 == 1;"),
            source.replace("1 <= to_integer(b)", "0 <= to_integer(b)"),
            source.replace("to_integer(b) != 0", "to_integer(b) == 0"),
        ] {
            let path = project.directory.join("false.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(error.message().len() < 8000, "bounded refusal");
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn wide_narrowing_integer_ranges_reflect_into_native_correction_bounds() {
    for (name, ty, suffix) in [
        ("ss32", "int32", ""),
        ("ss64", "int64", "i64"),
        ("relay", "int64", "i64"),
    ] {
        let project = Project::with_fixture("narrow.cpp", name, WIDE_NARROWING_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let cert = cast_identity_proof("to_integer(a)", "-100", "100");
        let helper = if name == "relay" { "ss64" } else { name };
        let mut proof = format!(
            r#"import click::integer;
verifying "narrow.cpp";
{ty} {helper}(int128 a) {{
    requires -100 <= to_integer(a);
    requires to_integer(a) <= 100;
    ensures -100{suffix} <= result;
    ensures result <= 100{suffix};
}} by {{
    step_until(function.exit);
    have to_integer(result) == to_integer(a) by {{ {cert} }}
    have -100 <= to_integer(result) by {{ close() using {{ to_integer(result) == to_integer(a); -100 <= to_integer(a); }}; }}
    have to_integer(result) <= 100 by {{ close() using {{ to_integer(result) == to_integer(a); to_integer(a) <= 100; }}; }}
    close();
}}"#
        );
        if name == "relay" {
            proof.push_str(
                r#"
int64 relay(int128 a, int32* untouched) {
    requires -100 <= to_integer(a);
    requires to_integer(a) <= 100;
    owns untouched[0..1];
    ensures -100i64 <= result;
    ensures result <= 100i64;
    ensures untouched[0] == old(untouched[0]);
}
"#,
            );
            check_selected_claim_certificate(&project, &import, &proof);
        } else {
            check_first_claim_certificate(&project, &import, &proof);
        }
        for hostile in [
            proof.replace("requires -100 <= to_integer(a);", ""),
            proof.replace("requires to_integer(a) <= 100;", ""),
            proof.replace(
                &format!("ensures result <= 100{suffix};"),
                &format!("ensures result <= 99{suffix};"),
            ),
        ] {
            let path = project.directory.join("false.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
            assert!(error.message().len() < 8000);
        }
    }
}

fn check_fee_rounding_pattern(name: &str, rejections: bool) {
    let project = Project::with_fixture(
        "round.cpp",
        name,
        include_str!("fixtures/cpp-verification/fee-rounding/round.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let mut proof = include_str!("fixtures/cpp-verification/fee-rounding/Rounded.click").to_owned();
    if name == "caller" {
        proof.push_str(
            r#"
int64 caller(int128 n, int32 d, bool round_down, int32* untouched) {
requires -9223372036854775808 * to_integer(d) <= to_integer(n);
requires to_integer(n) <= 9223372036854775807 * to_integer(d);
requires d > 0;
requires d <= 100;
owns untouched[0..1];
ensures untouched[0] == old(untouched[0]);
ensures -9223372036854775808i64 <= result;
ensures result <= 9223372036854775807i64;
ensures round_down == true and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1;
ensures round_down == true and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
ensures round_down == false and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1;
ensures round_down == false and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
ensures round_down == true implies to_integer(result) * to_integer(d) <= to_integer(n);
ensures round_down == true implies to_integer(n) < (to_integer(result) + 1) * to_integer(d);
ensures round_down == false implies to_integer(n) <= to_integer(result) * to_integer(d);
ensures round_down == false implies (to_integer(result) + -1) * to_integer(d) < to_integer(n);
}
"#,
        );
    }
    let path = project.directory.join("complete.click");
    fs::write(&path, &proof).unwrap();
    let parsed = read_click_project(&path, &proof).unwrap();
    if !rejections {
        let inputs = ProgramInputs::program(&import);
        let sites = project_smart_tactic_source_sites(&parsed, &inputs).unwrap();
        let selected = if name == "caller" {
            sites
                .iter()
                .find(|site| site.claim_label.starts_with("caller."))
                .unwrap()
        } else {
            sites.first().unwrap()
        };
        let (session, verified) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        // Spell both claims before any cold check resets the certificate tables.
        let expanded = click::surface::expand_verified_function_claim_source_by_label(
            &proof,
            &verified,
            &selected.claim_label,
        )
        .unwrap()
        .unwrap();
        let rounded = click::surface::expand_verified_function_claim_source_by_label(
            &proof,
            &verified,
            "rounded.ensures_0",
        )
        .unwrap()
        .unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        let position =
            project_tactic_source_position(&rewritten, &inputs, &selected.claim_label, 0).unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
        drop(session);
        verify_program_prepared_project(&rewritten, &import).unwrap();
        // A member of a grouped claim can spell the exact same complete proof.
        // A distinct rounded-function output still gets its own full cold check.
        if rounded != expanded {
            verify_program_prepared_project(&parsed.with_entry_source(rounded), &import).unwrap();
        }
        return;
    }
    for hostile in [
            proof.replace(
                "round_down == true implies to_integer(result) * to_integer(d) <= to_integer(n)",
                "round_down == true implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),
            proof.replace(
                "round_down == true implies to_integer(n) < (to_integer(result) + 1) * to_integer(d)",
                "round_down == true implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            proof.replace(
                "round_down == false implies to_integer(n) <= to_integer(result) * to_integer(d)",
                "round_down == false implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            proof.replace(
                "round_down == false implies (to_integer(result) + -1) * to_integer(d) < to_integer(n)",
                "round_down == false implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),

        proof.replace("requires -9223372036854775808 * to_integer(d) <= to_integer(n);", ""),
        proof.replace("requires to_integer(n) <= 9223372036854775807 * to_integer(d);", ""),
        proof.replace("requires -9223372036854775808 * to_integer(d) <= to_integer(n);", "requires -9223372036854775809 * to_integer(d) <= to_integer(n);"),
        proof.replace("requires to_integer(n) <= 9223372036854775807 * to_integer(d);", "requires to_integer(n) <= 9223372036854775808 * to_integer(d);"),
        proof.replace("apply(integer::upper_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), 9223372036854775807));", ""),
        proof.replace("apply(integer::lower_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), -9223372036854775808));", ""),
        proof.replace("requires d > 0;", ""),
        proof.replace("requires d <= 100;", ""),
        proof.replace("requires d > 0;", "requires d == 0;"),
        proof.replace(
            "ensures -9223372036854775808 <= to_integer(result);",
            "ensures to_integer(result) == 1000;",
        ),

        proof.replace(
            "round_down == true and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1",
            "round_down == true and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
        ),
        proof.replace(
            "round_down == false and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
            "round_down == false and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1",
        ),
        proof.replace(
            "round_down == true and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d))",
            "round_down == true and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
        ),
        proof.replace(
            "round_down == false and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d))",
            "round_down == false and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1",
        ),
        proof.replace(
            "have to_integer(quot + 1i64) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
            "have to_integer(quot + 1i64) == truncating_quotient(to_integer(n), to_integer(d)) + 2",
        ),
        proof.replace(
            "have to_integer(quot + -1i64) == truncating_quotient(to_integer(n), to_integer(d)) + -1",
            "have to_integer(quot + -1i64) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
        ),
    ] {
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        let Err(error) = verify_program_prepared_project(&parsed, &import) else {
            panic!("hostile rounding claim must be refused");
        };
        assert!(error.message().len() < 8000);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn fee_rounding_pattern_has_checked_native_correction_bounds() {
    check_fee_rounding_pattern("rounded", false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn fee_rounding_pattern_modular_caller_has_exact_rounding_values() {
    check_fee_rounding_pattern("caller", false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn fee_rounding_pattern_rejects_false_rounding_and_missing_guards() {
    check_fee_rounding_pattern("rounded", true);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn fee_rounding_pattern_caller_rejects_false_rounding_and_missing_guards() {
    check_fee_rounding_pattern("caller", true);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn symbolic_wide_field_branch_paths_keep_their_selector_width() {
    let cpp = include_str!("fixtures/cpp-verification/branch-paths/wide-field.cpp");
    let project = Project::with_fixture("wide-field.cpp", "choose", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "wide-field.cpp";
int32 choose(const struct Box& box) {
 views box.fee;
 ensures result == 1 or result == 2;
 ensures box.fee == old(box.fee);
}
"#;
    check_arithmetic_sidecar(&project, &import, source);
    for (fee, result) in [("-1i64", 2), ("1i64", 1), ("8589934592i64", 2)] {
        let precise = source
            .replace(
                "views box.fee;",
                &format!("views box.fee;\n requires box.fee == {fee};"),
            )
            .replace("result == 1 or result == 2", &format!("result == {result}"));
        check_arithmetic_sidecar(&project, &import, &precise);
    }
    for bad in [
        source.replace("views box.fee;", ""),
        source.replace("result == 1 or result == 2", "result == 1"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn class_records_preserve_private_and_protected_field_layout_and_authority() {
    let source = include_str!("fixtures/cpp-verification/class-record/class_record.cpp");
    for access in ["private:", "protected:", ""] {
        for (selected, sidecar) in [
            (
                "FeeRateState::IsEmpty",
                include_str!("fixtures/cpp-verification/class-record/is_empty.click"),
            ),
            (
                "FeeRateState::ReadFee",
                include_str!("fixtures/cpp-verification/class-record/read_fee.click"),
            ),
            (
                "FeeRateState::SetFee",
                include_str!("fixtures/cpp-verification/class-record/set_fee.click"),
            ),
        ] {
            let project = Project::with_fixture(
                "class_record.cpp",
                selected,
                &source.replace("private:", access),
            );
            refresh_import(&project.config()).unwrap();
            let import = load_import(&project.config()).unwrap();
            let [record] = import.export().records.as_slice() else {
                panic!("one class layout")
            };
            assert_eq!(record.name, "FeeRateState");
            assert_eq!(record.size_bytes, 16);
            assert_eq!(record.alignment_bytes, 8);
            assert_eq!(
                record
                    .fields
                    .iter()
                    .map(|f| (f.name.as_str(), f.offset_bytes, f.size_bytes))
                    .collect::<Vec<_>>(),
                [("fee", 0, 8), ("size", 8, 4)]
            );
            fs::remove_file(&project.exporter).unwrap();
            let import = load_import(&project.config()).unwrap();
            check_return_call_sidecar(&project, &import, sidecar);
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn class_record_proofs_reject_missing_authority_false_frames_and_readonly_writes() {
    let source = include_str!("fixtures/cpp-verification/class-record/class_record.cpp");
    for (selected, original, mutants) in [
        (
            "FeeRateState::IsEmpty",
            include_str!("fixtures/cpp-verification/class-record/is_empty.click"),
            vec![
                ("views this->size;", ""),
                ("result == (if", "result != (if"),
            ],
        ),
        (
            "FeeRateState::ReadFee",
            include_str!("fixtures/cpp-verification/class-record/read_fee.click"),
            vec![
                ("views this->fee;", ""),
                ("result == old(this->fee)", "result != old(this->fee)"),
            ],
        ),
        (
            "FeeRateState::SetFee",
            include_str!("fixtures/cpp-verification/class-record/set_fee.click"),
            vec![
                ("owns this->fee;", ""),
                ("owns this->fee;", "views this->fee;"),
                ("this->fee == next", "this->fee == old(this->fee)"),
                (
                    "this->size == old(this->size)",
                    "this->size != old(this->size)",
                ),
            ],
        ),
    ] {
        let project = Project::with_fixture("class_record.cpp", selected, source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        for (before, after) in mutants {
            let hostile = original.replace(before, after);
            assert_ne!(hostile, original);
            let sidecar = project.directory.join("hostile.click");
            fs::write(&sidecar, &hostile).unwrap();
            let parsed = read_click_project(&sidecar, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("class field proof accepted missing authority or false claim");
            };
            assert!(error.message().len() < 8000);
        }
    }
}

#[test]
fn class_record_import_keeps_cpp_access_control_and_layout_restrictions() {
    let source = include_str!("fixtures/cpp-verification/class-record/class_record.cpp");
    for (access, diagnostic) in [
        ("private:", "private member"),
        ("protected:", "protected member"),
    ] {
        let invalid = format!(
            "{}\nlong long read_external(const FeeRateState& state) {{ return state.fee; }}\n",
            source.replace("private:", access)
        );
        let project = Project::with_fixture("class_record.cpp", "read_external", &invalid);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
    for (invalid, diagnostic) in [
        (
            source.replace("class FeeRateState", "union FeeRateState"),
            "named struct or class",
        ),
        (
            source.replace("    int size;", "public:\n    int size;"),
            "standard-layout",
        ),
        (
            source.replace(
                "class FeeRateState {",
                "struct Base { int value; };\nclass FeeRateState : public Base {",
            ),
            "no own fields",
        ),
        (
            source.replace("    int size;", "    int size : 4;"),
            "without bit-fields",
        ),
    ] {
        let project = Project::with_fixture("class_record.cpp", "FeeRateState::IsEmpty", &invalid);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn record_refusal_diagnostics_keep_macro_expansion_source_and_line_together() {
    let mut project = Project::with_fixture(
        "record_macro.cpp",
        "read_value",
        "#include \"layout.h\"\nBAD_RECORD(State)\nint read_value(const State& state) noexcept { return state.value; }\n",
    );
    fs::write(
        project.directory.join("layout.h"),
        "#define BAD_RECORD(name) struct name { int value : 4; };\n",
    )
    .unwrap();
    project.dependencies.push("layout.h".into());
    project.write_config("read_value");
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("record_macro.cpp:2:"), "{error}");
    assert!(error.contains("without bit-fields"), "{error}");
    assert!(!error.contains("layout.h:2:"), "{error}");
    assert!(!project.artifact().exists());
}

fn header_record_project(selected: &str) -> Project {
    let mut project = Project::with_fixture(
        "header_record.cpp",
        selected,
        include_str!("fixtures/cpp-verification/header-record/header_record.cpp"),
    );
    fs::write(
        project.directory.join("state.h"),
        include_str!("fixtures/cpp-verification/header-record/state.h"),
    )
    .unwrap();
    project.dependencies.push("state.h".into());
    project.write_config(selected);
    project
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn locked_header_records_preserve_declaration_sources_and_verify_offline() {
    for (selected, sidecar) in [
        (
            "FeeRateState::IsEmpty",
            include_str!("fixtures/cpp-verification/class-record/is_empty.click"),
        ),
        (
            "FeeRateState::ReadFee",
            include_str!("fixtures/cpp-verification/class-record/read_fee.click"),
        ),
        (
            "FeeRateState::SetFee",
            include_str!("fixtures/cpp-verification/class-record/set_fee.click"),
        ),
    ] {
        let project = header_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [record] = import.export().records.as_slice() else {
            panic!("only the reachable record")
        };
        assert_eq!(record.name, "FeeRateState");
        assert_eq!(record.span.file, "state.h");
        assert_eq!(record.size_bytes, 16);
        assert_eq!(record.alignment_bytes, 8);
        for field in &record.fields {
            assert_eq!(field.span.file, "state.h");
        }
        assert_eq!(import.export().dependencies, ["state.h"]);
        assert_eq!(import.export().functions[0].span.file, "header_record.cpp");
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        check_return_call_sidecar(
            &project,
            &import,
            &sidecar.replace("class_record.cpp", "header_record.cpp"),
        );
    }
}

#[test]
fn header_records_require_explicit_dependencies_and_reject_stale_header_bytes() {
    let mut project = header_record_project("FeeRateState::ReadFee");
    project.dependencies.clear();
    project.write_config("FeeRateState::ReadFee");
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("differ from configured dependencies"),
        "{error}"
    );
    assert!(!project.artifact().exists());
    project.dependencies.push("state.h".into());
    project.write_config("FeeRateState::ReadFee");
    refresh_import(&project.config()).unwrap();
    let original = load_import(&project.config())
        .unwrap()
        .identity()
        .to_owned();
    let header = project.directory.join("state.h");
    let changed = format!(
        "{}\n// changed locked input\n",
        fs::read_to_string(&header).unwrap()
    );
    fs::write(&header, changed).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(
        error.contains("dependency") || error.contains("preprocessor"),
        "{error}"
    );
    refresh_import(&project.config()).unwrap();
    assert_ne!(load_import(&project.config()).unwrap().identity(), original);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn header_record_artifacts_reject_forged_declaration_and_executable_sources() {
    use sha2::{Digest, Sha256};
    for change in ["record", "field", "field_owner", "function"] {
        let project = header_record_project("FeeRateState::ReadFee");
        refresh_import(&project.config()).unwrap();
        let mut artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let mut lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        match change {
            "record" => artifact["records"][0]["span"]["file"] = "unlisted.h".into(),
            "field" => artifact["records"][0]["fields"][0]["span"]["file"] = "unlisted.h".into(),
            "field_owner" => {
                artifact["records"][0]["fields"][0]["span"]["file"] = "header_record.cpp".into()
            }
            "function" => artifact["functions"][0]["span"]["file"] = "state.h".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(
            error.contains("source span") || error.contains("different source"),
            "{error}"
        );
    }
}

fn nested_record_project(selected: &str) -> Project {
    let mut project = Project::with_fixture(
        "nested_record.cpp",
        selected,
        include_str!("fixtures/cpp-verification/nested-record/nested_record.cpp"),
    );
    fs::write(
        project.directory.join("state.h"),
        include_str!("fixtures/cpp-verification/nested-record/state.h"),
    )
    .unwrap();
    project.dependencies.push("state.h".into());
    project.write_config(selected);
    project
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn nested_record_declarations_preserve_layout_identity_and_offline_field_frames() {
    use click::languages::cpp::CppType;
    for (selected, sidecar) in [
        (
            "FeeEnvelope::SetStamp",
            include_str!("fixtures/cpp-verification/nested-record/set_stamp.click"),
        ),
        (
            "FeeEnvelope::ReadStamp",
            include_str!("fixtures/cpp-verification/nested-record/read_stamp.click"),
        ),
    ] {
        let project = nested_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let records = &import.export().records;
        assert_eq!(records.len(), 3);
        let leaf = records
            .iter()
            .find(|record| record.name == "FeeState")
            .unwrap();
        let pair = records
            .iter()
            .find(|record| record.name == "PairState")
            .unwrap();
        let outer = records
            .iter()
            .find(|record| record.name == "FeeEnvelope")
            .unwrap();
        assert_eq!(
            (leaf.size_bytes, pair.size_bytes, outer.size_bytes),
            (16, 40, 48)
        );
        assert_eq!(
            pair.fields
                .iter()
                .map(|field| field.offset_bytes)
                .collect::<Vec<_>>(),
            [0, 16, 32]
        );
        assert_eq!(
            outer
                .fields
                .iter()
                .map(|field| field.offset_bytes)
                .collect::<Vec<_>>(),
            [0, 40]
        );
        for field in &pair.fields[..2] {
            assert!(
                matches!(&field.value_type, CppType::Record { declaration_id, name, is_const: false } if declaration_id == &leaf.declaration_id && name == "FeeState")
            );
            assert_eq!(field.size_bytes, 16);
        }
        assert!(
            matches!(&outer.fields[0].value_type, CppType::Record { declaration_id, .. } if declaration_id == &pair.declaration_id)
        );
        for record in records {
            assert_eq!(record.span.file, "state.h");
        }
        fs::remove_file(&project.exporter).unwrap();
        check_selected_claim_certificate(
            &project,
            &load_import(&project.config()).unwrap(),
            sidecar,
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn nested_record_contracts_reject_missing_authority_false_frames_and_readonly_writes() {
    let sidecar = include_str!("fixtures/cpp-verification/nested-record/set_stamp.click");
    let project = nested_record_project("FeeEnvelope::SetStamp");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    for invalid in [
        sidecar.replace("    owns this->stamp;\n", ""),
        sidecar.replace(
            "ensures this->state.right.fee == old(this->state.right.fee);",
            "ensures this->state.right.fee == old(this->state.left.fee);",
        ),
        sidecar.replace("owns this->stamp;", "views this->stamp;"),
    ] {
        let path = project.directory.join("hostile.click");
        fs::write(&path, &invalid).unwrap();
        let parsed = read_click_project(&path, &invalid).unwrap();
        let Err(error) = verify_program_prepared_project(&parsed, &import) else {
            panic!("invalid nested field contract verified")
        };
        assert!(error.message().len() < 8000);
    }
}

#[test]
fn nested_record_artifacts_reject_wrong_identity_size_constness_and_cycles() {
    use sha2::{Digest, Sha256};
    let project = nested_record_project("FeeEnvelope::ReadStamp");
    refresh_import(&project.config()).unwrap();
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let original_lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    let pair = original["records"]
        .as_array()
        .unwrap()
        .iter()
        .position(|record| record["name"] == "PairState")
        .unwrap();
    let leaf = original["records"]
        .as_array()
        .unwrap()
        .iter()
        .position(|record| record["name"] == "FeeState")
        .unwrap();
    for change in [
        "identity",
        "name",
        "width",
        "offset",
        "alignment",
        "const",
        "missing",
        "cycle",
    ] {
        let mut artifact = original.clone();
        let field = &mut artifact["records"][pair]["fields"][0];
        match change {
            "identity" => field["value_type"]["declaration_id"] = "unknown".into(),
            "name" => field["value_type"]["name"] = "OtherState".into(),
            "width" => field["size_bytes"] = 8.into(),
            "offset" => field["offset_bytes"] = 4.into(),
            "alignment" => artifact["records"][pair]["alignment_bytes"] = 4.into(),
            "const" => field["value_type"]["is_const"] = true.into(),
            "missing" => {
                artifact["records"].as_array_mut().unwrap().remove(leaf);
            }
            "cycle" => {
                let id = artifact["records"][leaf]["declaration_id"].clone();
                artifact["records"][leaf]["fields"]
                    .as_array_mut()
                    .unwrap()
                    .truncate(1);
                artifact["records"][leaf]["fields"][0]["value_type"] = serde_json::json!({"kind":"record", "declaration_id":id, "name":"FeeState", "is_const":false});
                artifact["records"][leaf]["fields"][0]["size_bytes"] = 16.into();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock = original_lock.clone();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{change}: {error}");
        assert!(
            error.contains("record") || error.contains("layout"),
            "{change}: {error}"
        );
        if change == "cycle" {
            assert!(error.contains("by-value cycle"), "{error}");
        }
    }
}

#[test]
fn nested_record_qualified_and_pointer_fields_and_nontrivial_destruction_remain_boundaries() {
    for (declaration, body) in [
        ("const FeeState state;", "return stamp;"),
        ("mutable FeeState state;", "return stamp;"),
        // A pointer to a mutable record is a supported field; one to a const
        // record is not.
        ("const FeeState* state;", "return stamp;"),
    ] {
        let source = format!(
            "struct FeeState {{ int size; }}; struct Envelope {{ {declaration} int stamp; int Read() const noexcept {{ {body} }} }};"
        );
        let project = Project::with_fixture("nested.cpp", "Envelope::Read", &source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{error}");
        assert!(!project.artifact().exists());
    }
    let project = Project::with_fixture(
        "nested.cpp",
        "Envelope::Read",
        "struct Child { int size; ~Child() noexcept { size = 0; } }; struct Envelope { Child state; int stamp; int Read() const noexcept { return stamp; } };",
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("trivial destruction") || error.contains("trivially copyable"),
        "{error}"
    );
    assert!(!project.artifact().exists());
}

#[test]
fn nested_record_shared_layout_expansion_has_a_bounded_leaf_budget() {
    let mut source = "struct R0 { int value; };\n".to_owned();
    for level in 1..=17 {
        source.push_str(&format!(
            "struct R{level} {{ R{} left; R{} right; }};\n",
            level - 1,
            level - 1
        ));
    }
    source.push_str("struct Envelope { R17 state; int Read() const noexcept { return 0; } };\n");
    let project = Project::with_fixture("nested.cpp", "Envelope::Read", &source);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = "verifying \"nested.cpp\"; int Envelope::Read() const { ensures result == 0; }";
    let path = project.directory.join("budget.click");
    fs::write(&path, sidecar).unwrap();
    let parsed = read_click_project(&path, sidecar).unwrap();
    let Err(error) = verify_program_prepared_project(&parsed, &import) else {
        panic!("unbounded layout expansion accepted")
    };
    assert!(
        error
            .message()
            .contains("materialized record layout leaves"),
        "{}",
        error.message()
    );
    assert!(error.message().len() < 8000);
}

#[test]
fn nested_record_exporter_counts_pending_declarations_in_the_inventory_budget() {
    for count in [256, 257] {
        let mut source = "struct R0 { int value; };\n".to_owned();
        for level in 1..count {
            source.push_str(&format!("struct R{level} {{ R{} state; }};\n", level - 1));
        }
        source.push_str(&format!(
            "int read(const R{}& state) noexcept {{ return 0; }}\n",
            count - 1
        ));
        let project = Project::with_fixture("nested.cpp", "read", &source);
        if count == 256 {
            refresh_import(&project.config()).unwrap();
            assert_eq!(
                load_import(&project.config())
                    .unwrap()
                    .export()
                    .records
                    .len(),
                count
            );
        } else {
            let error = refresh_import(&project.config()).unwrap_err();
            assert!(error.contains("record declarations (limit 256)"), "{error}");
            assert!(error.len() < 8000);
            assert!(!project.artifact().exists());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn nested_source_fields_read_write_and_update_with_exact_authority_offline() {
    for (selected, sidecar) in [
        (
            "FeeEnvelope::ReadLeftFee",
            include_str!("fixtures/cpp-verification/nested-record/read_left_fee.click"),
        ),
        (
            "FeeEnvelope::SetRightFee",
            include_str!("fixtures/cpp-verification/nested-record/set_right_fee.click"),
        ),
        (
            "FeeEnvelope::AddLeftSize",
            include_str!("fixtures/cpp-verification/nested-record/add_left_size.click"),
        ),
        (
            "ReadRightFee",
            include_str!("fixtures/cpp-verification/nested-record/read_right_fee.click"),
        ),
    ] {
        let project = nested_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let body = &import.export().functions[0].body;
        let object = match &body[0] {
            CppStatement::MemberStore { object, .. } => object,
            CppStatement::Return {
                value: CppExpression::MemberLoad { object, .. },
                ..
            } => object,
            _ => panic!("expected projected access"),
        };
        assert_eq!(
            object
                .projections
                .iter()
                .map(|projection| match projection {
                    CppProjection::Field(field) => field.name.as_str(),
                    CppProjection::Base { .. } => panic!("expected an embedded field path"),
                })
                .collect::<Vec<_>>(),
            if selected == "ReadRightFee" {
                vec!["right"]
            } else if selected == "FeeEnvelope::SetRightFee" {
                vec!["state", "right"]
            } else {
                vec!["state", "left"]
            }
        );
        fs::remove_file(&project.exporter).unwrap();
        check_selected_claim_certificate(
            &project,
            &load_import(&project.config()).unwrap(),
            sidecar,
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn nested_source_field_contracts_reject_missing_and_sibling_authority_false_frames_and_views() {
    for (selected, sidecar, mutants) in [
        (
            "FeeEnvelope::ReadLeftFee",
            include_str!("fixtures/cpp-verification/nested-record/read_left_fee.click"),
            vec![
                ("views this->state.left.fee;", ""),
                (
                    "views this->state.left.fee;",
                    "views this->state.right.fee;",
                ),
                (
                    "result == this->state.left.fee",
                    "result != this->state.left.fee",
                ),
            ],
        ),
        (
            "FeeEnvelope::SetRightFee",
            include_str!("fixtures/cpp-verification/nested-record/set_right_fee.click"),
            vec![
                (
                    "owns this->state.right.fee;",
                    "views this->state.right.fee;",
                ),
                ("owns this->state.right.fee;", "owns this->state.left.fee;"),
                (
                    "this->state.left.fee == old(this->state.left.fee)",
                    "this->state.left.fee == next",
                ),
            ],
        ),
        (
            "FeeEnvelope::AddLeftSize",
            include_str!("fixtures/cpp-verification/nested-record/add_left_size.click"),
            vec![
                ("requires this->state.left.size <= 10;", ""),
                (
                    "this->state.right.size == old(this->state.right.size)",
                    "this->state.right.size != old(this->state.right.size)",
                ),
            ],
        ),
    ] {
        let project = nested_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        for (before, after) in mutants {
            let hostile = sidecar.replace(before, after);
            assert_ne!(hostile, sidecar);
            let path = project.directory.join("hostile.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("invalid projected field proof accepted: {before}")
            };
            assert!(error.message().len() < 8000);
        }
    }
}

#[test]
fn nested_source_field_artifacts_reject_forged_paths_readonly_roots_and_unimplemented_places() {
    use sha2::{Digest, Sha256};
    let project = nested_record_project("FeeEnvelope::SetRightFee");
    refresh_import(&project.config()).unwrap();
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let original_lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for change in [
        "owner",
        "field",
        "name",
        "source",
        "order",
        "missing",
        "scalar",
        "depth",
        "readonly",
        "plain_load",
    ] {
        let mut artifact = original.clone();
        let object = &mut artifact["functions"][0]["body"][0]["object"];
        match change {
            "owner" => object["projections"][0]["record_declaration_id"] = "unknown".into(),
            "field" => object["projections"][1]["declaration_id"] = "unknown".into(),
            "name" => object["projections"][1]["name"] = "left".into(),
            "source" => object["projections"][1]["span"]["file"] = "state.h".into(),
            "order" => object["projections"].as_array_mut().unwrap().reverse(),
            "missing" => {
                object["projections"].as_array_mut().unwrap().pop();
            }
            "scalar" => {
                let leaf = artifact["functions"][0]["body"][0]["field"].clone();
                artifact["functions"][0]["body"][0]["object"]["projections"]
                    .as_array_mut()
                    .unwrap()
                    .push(leaf);
            }
            "depth" => {
                let step = object["projections"][0].clone();
                object["projections"] = vec![step; 257].into();
            }
            "readonly" => {
                artifact["functions"][0]["function_kind"]["is_const"] = true.into();
                artifact["functions"][0]["parameters"][0]["value_type"]["pointee"]["is_const"] =
                    true.into();
            }
            "plain_load" => {
                let parameter = artifact["functions"][0]["parameters"][1].clone();
                let span = artifact["functions"][0]["body"][0]["span"].clone();
                artifact["functions"][0]["body"][0]["value"] = serde_json::json!({"kind":"load", "place":{"declaration_id":parameter["declaration_id"], "name":parameter["name"], "span":span, "projections":original["functions"][0]["body"][0]["object"]["projections"]}, "value_type":parameter["value_type"], "span":span});
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock = original_lock.clone();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{change}: {error}");
        if change == "readonly" {
            assert!(error.contains("const record reference"), "{error}");
        }
        if change == "plain_load" {
            assert!(error.contains("unsupported in this operation"), "{error}");
        }
    }
}

#[test]
fn nested_source_fields_keep_cpp_access_checks() {
    for source in [
        "struct Child { int value; }; struct Outer { Child child; }; void write(const Outer& root) noexcept { root.child.value = 1; }",
        "struct Child { int value; }; class Outer { Child child; }; int write(const Outer& root) noexcept { return root.child.value; }",
    ] {
        let project = Project::with_fixture("nested.cpp", "write", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn nested_pointer_fields_keep_const_object_and_pointee_authority_separate() {
    let source = "struct Child { int* pointer; }; struct Outer { Child child; int stamp; }; int read(const Outer& state, int* value) noexcept { return *state.child.pointer; } void write(const Outer& state, int* value, int next) noexcept { *state.child.pointer = next; }";
    for (selected, sidecar) in [
        (
            "read",
            "verifying \"pointer_nested.cpp\"; int read(const struct Outer& state, int* value) { views state.child.pointer; views value[0..1]; requires state.child.pointer == value; ensures result == value[0]; }",
        ),
        (
            "write",
            "verifying \"pointer_nested.cpp\"; void write(const struct Outer& state, int* value, int next) { views state.child.pointer; owns value[0..1]; requires state.child.pointer == value; ensures value[0] == next; ensures state.child.pointer == old(state.child.pointer); }",
        ),
    ] {
        let project = Project::with_fixture("pointer_nested.cpp", selected, source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        check_selected_claim_certificate(&project, &import, sidecar);
        let hostile = sidecar
            .replace("views value[0..1];", "")
            .replace("owns value[0..1];", "views value[0..1];");
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        let Err(error) = verify_program_prepared_project(&parsed, &import) else {
            panic!("nested pointer access accepted insufficient pointee authority")
        };
        assert!(error.message().len() < 8000);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn projected_record_calls_and_reference_arguments_verify_offline() {
    for (selected, sidecar, expected) in [
        (
            "FeeEnvelope::ReadLeftByMethod",
            include_str!("fixtures/cpp-verification/nested-record/projected_read.click"),
            vec!["state", "left"],
        ),
        (
            "FeeEnvelope::SetRightByMethod",
            include_str!("fixtures/cpp-verification/nested-record/projected_write.click"),
            vec!["state", "right"],
        ),
        (
            "FeeEnvelope::ReadRightByReference",
            include_str!("fixtures/cpp-verification/nested-record/reference_read.click"),
            vec!["state", "right"],
        ),
        (
            "FeeEnvelope::SetLeftByReference",
            include_str!("fixtures/cpp-verification/nested-record/reference_write.click"),
            vec!["state", "left"],
        ),
        (
            "FeeEnvelope::BumpLeftByReference",
            include_str!("fixtures/cpp-verification/nested-record/reference_bump.click"),
            vec!["state", "left", "size"],
        ),
        (
            "FeeEnvelope::ReadRightSizeByReference",
            include_str!("fixtures/cpp-verification/nested-record/reference_size_read.click"),
            vec!["state", "right", "size"],
        ),
    ] {
        let project = nested_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let arguments = match &import.export().functions[0].body[0] {
            CppStatement::ReturnCall { arguments, .. } | CppStatement::Call { arguments, .. } => {
                arguments
            }
            _ => panic!("expected projected call"),
        };
        let CppCallArgument::Reference { place } = &arguments[0] else {
            panic!("expected projected reference")
        };
        assert_eq!(
            place
                .projections
                .iter()
                .map(|projection| match projection {
                    CppProjection::Field(field) => field.name.as_str(),
                    CppProjection::Base { .. } => panic!("expected an embedded field path"),
                })
                .collect::<Vec<_>>(),
            expected
        );
        assert_eq!(import.export().reachable_functions.len(), 1);
        fs::remove_file(&project.exporter).unwrap();
        check_selected_claim_certificate(
            &project,
            &load_import(&project.config()).unwrap(),
            sidecar,
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn projected_call_artifacts_check_target_identity_and_root_constness() {
    use sha2::{Digest, Sha256};
    for selected in [
        "FeeEnvelope::SetRightByMethod",
        "FeeEnvelope::SetLeftByReference",
        "FeeEnvelope::BumpLeftByReference",
    ] {
        let project = nested_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let original: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let original_lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        for change in [
            "readonly",
            "owner",
            "field",
            "name",
            "source",
            "order",
            "missing",
            "depth",
            "root",
            "root_name",
        ] {
            let mut artifact = original.clone();
            let place = &mut artifact["functions"][0]["body"][0]["arguments"][0]["place"];
            match change {
                "readonly" => {
                    artifact["functions"][0]["function_kind"]["is_const"] = true.into();
                    artifact["functions"][0]["parameters"][0]["value_type"]["pointee"]["is_const"] =
                        true.into();
                }
                "owner" => place["projections"][0]["record_declaration_id"] = "unknown".into(),
                "field" => place["projections"][1]["declaration_id"] = "unknown".into(),
                "name" => place["projections"][1]["name"] = "unknown".into(),
                "source" => place["projections"][0]["span"]["file"] = "state.h".into(),
                "order" => place["projections"].as_array_mut().unwrap().reverse(),
                "missing" => {
                    place["projections"].as_array_mut().unwrap().pop();
                }
                "depth" => {
                    let step = place["projections"][0].clone();
                    place["projections"] = vec![step; 257].into();
                }
                "root" => place["declaration_id"] = "unknown".into(),
                "root_name" => place["name"] = "unknown".into(),
                _ => unreachable!(),
            }
            let bytes = serde_json::to_vec(&artifact).unwrap();
            let mut lock = original_lock.clone();
            lock_source_mut(&mut lock)["artifact"]["sha256"] =
                format!("{:x}", Sha256::digest(&bytes)).into();
            lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
            fs::write(project.artifact(), bytes).unwrap();
            fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
            let error = load_import(&project.config()).unwrap_err();
            assert!(error.len() < 8000, "{selected}/{change}: {error}");
            if change == "readonly" || change == "missing" {
                assert!(
                    error.contains("unsupported argument"),
                    "{selected}/{change}: {error}"
                );
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn projected_call_contracts_require_leaf_authority_and_preserve_sibling_frames() {
    for (selected, sidecar, mutants) in [
        (
            "FeeEnvelope::SetRightByMethod",
            include_str!("fixtures/cpp-verification/nested-record/projected_write.click"),
            vec![
                (
                    "owns this->state.right.fee;",
                    "views this->state.right.fee;",
                ),
                ("owns this->state.right.fee;", "owns this->state.left.size;"),
                (
                    "this->state.left.fee == old(this->state.left.fee)",
                    "this->state.left.fee == next",
                ),
                (
                    "this->state.right.fee == next",
                    "this->state.right.fee != next",
                ),
            ],
        ),
        (
            "FeeEnvelope::BumpLeftByReference",
            include_str!("fixtures/cpp-verification/nested-record/reference_bump.click"),
            vec![
                ("requires this->state.left.size <= 10;", ""),
                (
                    "owns this->state.left.size;",
                    "views this->state.left.size;",
                ),
                (
                    "this->state.right.size == old(this->state.right.size)",
                    "this->state.right.size != old(this->state.right.size)",
                ),
                ("requires value <= 10;", ""),
            ],
        ),
    ] {
        let project = nested_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        for (before, after) in mutants {
            let hostile = sidecar.replace(before, after);
            assert_ne!(hostile, sidecar);
            let path = project.directory.join("hostile.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("invalid projected call contract accepted: {selected}/{before}")
            };
            assert!(error.message().len() < 8000);
        }
    }
}

#[test]
fn projected_calls_keep_cpp_constness_and_source_profile_boundaries() {
    for source in [
        "struct Child { int value; void Set() noexcept { value = 1; } }; struct Outer { Child child; }; void run(const Outer& root) noexcept { root.child.Set(); }",
        "struct Child { int value; }; struct Outer { Child child; }; void Set(Child& value) noexcept { value.value = 1; } void run(const Outer& root) noexcept { Set(root.child); }",
        "struct Outer { int value; }; void Set(int& value) noexcept { value = 1; } void run(const Outer& root) noexcept { Set(root.value); }",
        // A record pointer parameter roots `root->child`; one read from a
        // field does not.
        "struct Child { int value; int Read() const noexcept { return value; } }; struct Outer { Child child; Outer* next; }; int run(Outer* root) noexcept { return root->next->child.Read(); }",
        "struct Child { int value; int Read() const noexcept { return value; } }; int run() noexcept { return Child{1}.Read(); }",
        "struct Outer { long long value; }; void Set(long long& value) noexcept { value = 1; } void run(Outer& root) noexcept { Set(root.value); }",
    ] {
        let project = Project::with_fixture("projected.cpp", "run", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn projected_calls_require_certified_callee_contracts_and_true_results() {
    for (selected, sidecar) in [
        (
            "FeeEnvelope::ReadLeftByMethod",
            include_str!("fixtures/cpp-verification/nested-record/projected_read.click"),
        ),
        (
            "FeeEnvelope::ReadRightByReference",
            include_str!("fixtures/cpp-verification/nested-record/reference_read.click"),
        ),
        (
            "FeeEnvelope::ReadRightSizeByReference",
            include_str!("fixtures/cpp-verification/nested-record/reference_size_read.click"),
        ),
    ] {
        let project = nested_record_project(selected);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (_, caller) = sidecar.split_once("}").unwrap();
        for hostile in [
            format!("verifying \"nested_record.cpp\";\n{caller}"),
            sidecar.replace("result ==", "result !="),
        ] {
            let path = project.directory.join("hostile.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let Err(error) = verify_program_prepared_project(&parsed, &import) else {
                panic!("projected call accepted missing or false callee contract: {selected}")
            };
            assert!(error.message().len() < 8000);
        }
    }
}

const CONDITION_CALL_SOURCE: &str = r#"
struct Base { int value; bool Empty() const noexcept { return value == 0; } };
struct Derived : Base {};
struct State { Derived left; int sibling; };
bool update(int& value, bool answer) noexcept { value = value + 1; return answer; }
int choose(State& state, bool answer) noexcept {
    if (update(state.sibling, answer)) { return 1; } else { return 2; }
}
int observe(const State& state) noexcept {
    if (state.left.Empty()) { return 1; } else { return 2; }
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn condition_calls_evaluate_once_before_branch_and_verify_offline() {
    let project = Project::with_fixture("condition.cpp", "choose", CONDITION_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[0],
        click::languages::cpp::CppStatement::If {
            condition: click::languages::cpp::CppCondition::Call { .. },
            ..
        }
    ));
    fs::remove_file(&project.exporter).unwrap();
    for (answer, expected) in [(false, 2), (true, 1)] {
        let sidecar = format!(
            r#"verifying "condition.cpp";
        bool update(int32& value, bool answer) {{ owns value; requires value == 4; ensures value == 5; ensures result == answer; }}
        int32 choose(struct State& state, bool answer) {{ owns state.sibling; views state.left.base.value; requires answer == {answer}; requires state.sibling == 4; ensures result == {expected}; ensures state.sibling == 5; ensures state.left.base.value == old(state.left.base.value); }}
        "#
        );
        check_selected_claim_certificate(&project, &import, &sidecar);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn condition_calls_preserve_inherited_receiver_and_sibling_frames() {
    let project = Project::with_fixture("condition.cpp", "observe", CONDITION_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    for (value, empty, expected) in [(0, true, 1), (3, false, 2)] {
        let sidecar = format!(
            r#"verifying "condition.cpp";
        bool Base::Empty() const {{ views this->value; ensures result == (if this->value == 0 {{ true }} else {{ false }}); }}
        int32 observe(const struct State& state) {{ views state.left.base.value; views state.sibling; requires state.left.base.value == {value}; ensures result == {expected}; ensures state.sibling == old(state.sibling); }} by {{
            step_until(call(0).entry);
            let {{ result: empty }} = step(Base::Empty, {{}});
            have empty == {empty} by {{
                rewrite(empty, (if state.left.base.value == 0 {{ true }} else {{ false }}));
                rewrite(state.left.base.value, {value});
                normalize();
            }}
            step_until(function.exit);
            close();
        }}
        "#
        );
        check_selected_claim_certificate(&project, &import, &sidecar);
        let hostile = sidecar.replace(&format!("result == {expected}"), "result == 9");
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
        let missing = sidecar.replace("views state.left.base.value;", "");
        fs::write(&path, &missing).unwrap();
        let parsed = read_click_project(&path, &missing).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn condition_calls_validate_target_result_arguments_and_metadata() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture("condition.cpp", "choose", CONDITION_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..8 {
        let mut forged = artifact.clone();
        let call = &mut forged["functions"][0]["body"][0]["condition"]["call"];
        match mutation {
            0 => call["callee"]["declaration_id"] = "missing".into(),
            1 => {
                call["value_type"] = serde_json::json!({"kind":"integer","bits":32,"signed":true,"is_const":false,"source_aliases":[]})
            }
            2 => call["arguments"] = serde_json::json!([]),
            3 => call["span"]["file"] = "unlocked.h".into(),
            4 => call["value_type"]["bits"] = 32.into(),
            5 => call["arguments"][0]["place"]["projections"] = serde_json::json!([]),
            6 => {
                forged["reachable_functions"][0]["return_type"] = serde_json::json!({"kind":"integer","bits":32,"signed":true,"is_const":false,"source_aliases":[]})
            }
            7 => call["callee"]["name"] = "wrong".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{error}");
    }
}

#[test]
fn condition_calls_refuse_unsupported_unary_plus() {
    let condition = "+predicate()";
    let source = format!(
        "bool predicate() noexcept {{ return true; }} int number() noexcept {{ return 1; }} int choose() noexcept {{ if ({condition}) {{ return 1; }} else {{ return 2; }} }}"
    );
    let project = Project::with_fixture("condition.cpp", "choose", &source);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.len() < 8000, "{error}");
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn expression_observers_admit_composed_boolean_conditions() {
    for condition in [
        "predicate() && predicate()",
        "predicate() == true",
        "number()",
    ] {
        let source = format!(
            "bool predicate() noexcept {{ return true; }} int number() noexcept {{ return 1; }} int choose() noexcept {{ if ({condition}) {{ return 1; }} else {{ return 2; }} }}"
        );
        let project = Project::with_fixture("condition.cpp", "choose", &source);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let (helper, result) = if condition == "number()" {
            ("int32 number()", "1")
        } else {
            ("bool predicate()", "true")
        };
        let sidecar = format!(
            r#"verifying "condition.cpp";
{helper} {{ ensures result == {result}; }}
int32 choose() {{ ensures result == 1; }}
"#
        );
        check_first_claim_certificate(&project, &import, &sidecar);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn condition_calls_propagate_scalar_exception_contracts() {
    let project = Project::with_fixture(
        "condition.cpp",
        "choose",
        "bool predicate(bool fail) { if (fail) { throw 7; } return true; } int choose(bool fail) { if (predicate(fail)) { return 5; } else { return 6; } }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("choose", "condition.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let source = r#"verifying "condition.cpp";
    bool predicate(bool fail) throws int32 { ensures result == true; exceptional ensures exception == 7; }
    int32 choose(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
    "#;
    check_selected_claim_certificate(&project, &import, source);
}

#[test]
fn condition_calls_unwind_active_objects_before_rethrow() {
    let source = r#"
struct Guard { int* slot; explicit Guard(int* value) noexcept : slot(value) { *slot = 1; } ~Guard() noexcept { *slot = 2; } };
bool predicate(bool fail) { if (fail) { throw 7; } return true; }
int choose(int* slot, bool fail) { Guard guard(slot); if (predicate(fail)) { *slot = 3; } else { *slot = 4; } return 5; }
"#;
    let project = Project::with_fixture("condition.cpp", "choose", source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("choose", "condition.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let lowered = lower_import(&load_import(&project.config()).unwrap()).unwrap();
    fn guarded_condition(statement: &ProgramStatement) -> bool {
        match statement {
            ProgramStatement::Seq(statements) => statements
                .iter()
                .any(|statement| guarded_condition(statement)),
            ProgramStatement::UnwindCleanup { body, cleanup } => {
                contains_call(body, "predicate") && contains_call(cleanup, "Guard::~Guard")
            }
            _ => false,
        }
    }
    assert!(guarded_condition(lowered.kernel_function().body()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn condition_calls_share_fresh_captures_with_nested_arguments_and_returns() {
    let project = Project::with_fixture(
        "condition.cpp",
        "choose",
        r#"
bool predicate(int value) noexcept { return value == 7; }
int echo(int value) noexcept { return value; }
int choose(int value) noexcept {
    int __click_cpp_nested_value_0 = 9;
    if (predicate(echo(value))) { if (predicate(value)) { return echo(__click_cpp_nested_value_0); } return 8; }
    return 0;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "condition.cpp";
    bool predicate(int32 value) { requires value == 7; ensures result == true; }
    int32 echo(int32 value) { ensures result == value; }
    int32 choose(int32 value) { requires value == 7; ensures result == 9; }
    "#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn condition_calls_preserve_the_enclosing_catch_scope() {
    let project = Project::with_fixture(
        "condition.cpp",
        "choose",
        "bool predicate(bool fail) { if (fail) { throw 7; } return true; } int choose(bool fail) { try { if (predicate(fail)) { return 5; } } catch (int caught) { return caught; } return 6; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("choose", "condition.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let sidecar = r#"verifying "condition.cpp";
        bool predicate(bool fail) throws int32 { ensures result == true; exceptional ensures exception == 7; }
        int32 choose(bool fail) { ensures result == 5 or result == 7; } by {
            outcomes {
                returned => { step_until(function.exit); close(); }
                threw => { step_until(function.exit); close(); }
            }
        }
    "#;
    check_selected_claim_certificate(&project, &import, sidecar);
    let hostile = sidecar.replace("result == 5 or result == 7", "result == 6");
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    let parsed = read_click_project(&path, &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn condition_calls_refuse_guarded_try_condition_hoisting() {
    use sha2::{Digest, Sha256};
    let source = r#"
struct Guard { int value; explicit Guard(int initial) noexcept : value(initial) {} ~Guard() noexcept { value = 0; } };
bool predicate(bool fail) { if (fail) { throw 7; } return true; }
int choose(bool fail) { predicate(fail); try { if (fail) { Guard guard(0); } } catch (int caught) { return caught; } return 5; }
"#;
    let project = Project::with_fixture("condition.cpp", "choose", source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("choose", "condition.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    let operation = artifact["functions"][0]["body"][0].clone();
    let span = artifact["functions"][0]["body"][1]["condition"]["span"].clone();
    artifact["functions"][0]["body"][1]["condition"] = serde_json::json!({"call": {
        "callee": operation["callee"], "arguments": operation["arguments"],
        "value_type": {"kind":"boolean","bits":8,"is_const":false}, "span":span
    }});
    let bytes = serde_json::to_vec(&artifact).unwrap();
    lock_source_mut(&mut lock)["artifact"]["sha256"] =
        format!("{:x}", Sha256::digest(&bytes)).into();
    lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
    fs::write(project.artifact(), bytes).unwrap();
    fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(
        error.contains("pure condition to preserve catch scope"),
        "{error}"
    );

    let project = Project::with_fixture(
        "condition.cpp",
        "choose",
        &source.replace("if (fail) { Guard", "if (predicate(fail)) { Guard"),
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("choose", "condition.cpp", true, "scalar_int32");
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.len() < 8000, "{error}");
    assert!(!project.artifact().exists());
    assert!(!project.lock().exists());
}

fn header_graph_project(selected: &str) -> Project {
    let mut project = Project::with_fixture(
        "graph.cpp",
        selected,
        r#"
#include "helpers.h"
int choose(const Box& state) noexcept { if (predicate(state.left)) { return 1; } else { return Read(state.left); } }
void change(Box& state, int next) noexcept { Store(state.left, next); }
"#,
    );
    fs::write(project.directory.join("types.h"), r#"
#pragma once
using Word = int;
struct Base { Word value; bool Empty() const noexcept { return value == 0; } void Set(Word next) noexcept { value = next; } };
struct Derived : Base {};
struct Box { Derived left; int sibling; };
"#).unwrap();
    fs::write(
        project.directory.join("helpers.h"),
        r#"
#pragma once
#include "types.h"
inline Word Read(const Base& state) noexcept { return state.value; }
inline void Store(Base& state, Word next) noexcept { state.Set(next); }
inline bool predicate(const Base& state) noexcept { return state.Empty(); }
"#,
    )
    .unwrap();
    project
        .dependencies
        .extend(["helpers.h".into(), "types.h".into()]);
    project.write_config(selected);
    project
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn locked_header_graph_conditions_verify_offline_with_inherited_frames() {
    let project = header_graph_project("choose");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().functions[0].span.file, "graph.cpp");
    for function in &import.export().reachable_functions {
        let source = if function.name.starts_with("Base_") {
            "types.h"
        } else {
            "helpers.h"
        };
        assert_eq!(function.span.file, source);
        assert!(
            function
                .parameters
                .iter()
                .all(|parameter| parameter.span.file == source)
        );
    }
    fs::remove_file(&project.exporter).unwrap();
    for (value, empty, result) in [(0, true, 1), (3, false, 3)] {
        let sidecar = format!(
            r#"verifying "graph.cpp";
        bool Base::Empty() const {{ views this->value; ensures result == (if this->value == 0 {{ true }} else {{ false }}); }}
        bool predicate(const struct Base& state) {{ views state.value; ensures result == (if state.value == 0 {{ true }} else {{ false }}); }}
        int32 Read(const struct Base& state) {{ views state.value; ensures result == state.value; }}
        int32 choose(const struct Box& state) {{ views state.left.base.value; views state.sibling; requires state.left.base.value == {value}; ensures result == {result}; ensures state.sibling == old(state.sibling); }} by {{
            step_until(call(0).entry);
            let {{ result: empty }} = step(predicate, {{}});
            have empty == {empty} by {{
                rewrite(empty, (if state.left.base.value == 0 {{ true }} else {{ false }}));
                rewrite(state.left.base.value, {value});
                normalize();
            }}
            step_until(function.exit);
            close();
        }}
        "#
        );
        check_selected_claim_certificate(&project, &import, &sidecar);
        let hostile = sidecar.replace(
            &format!("result == {result}; ensures state.sibling"),
            "result == 9; ensures state.sibling",
        );
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn locked_header_graph_mutators_verify_offline_and_require_leaf_authority() {
    let project = header_graph_project("change");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let sidecar = r#"verifying "graph.cpp";
    void Base::Set(int32 next) { owns this->value; ensures this->value == next; }
    void Store(struct Base& state, int32 next) { owns state.value; ensures state.value == next; }
    void change(struct Box& state, int32 next) { owns state.left.base.value; views state.sibling; ensures state.left.base.value == next; ensures state.sibling == old(state.sibling); }
    "#;
    check_selected_claim_certificate(&project, &import, sidecar);
    for hostile in [
        sidecar.replace(
            "owns state.left.base.value;",
            "views state.left.base.value;",
        ),
        sidecar.replace(
            "ensures state.sibling == old(state.sibling)",
            "ensures state.sibling == next",
        ),
    ] {
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
fn locked_header_graph_rejects_forged_body_call_and_alias_origins() {
    use sha2::{Digest, Sha256};
    let project = header_graph_project("choose");
    refresh_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    let predicate = artifact["reachable_functions"]
        .as_array()
        .unwrap()
        .iter()
        .position(|function| function["name"] == "predicate")
        .unwrap();
    let read = artifact["reachable_functions"]
        .as_array()
        .unwrap()
        .iter()
        .position(|function| function["name"] == "Read")
        .unwrap();
    for mutation in 0..8 {
        let mut forged = artifact.clone();
        match mutation {
            0 => forged["functions"][0]["span"]["file"] = "helpers.h".into(),
            1 => forged["reachable_functions"][predicate]["span"]["file"] = "types.h".into(),
            2 => {
                forged["reachable_functions"][predicate]["parameters"][0]["span"]["file"] =
                    "graph.cpp".into()
            }
            3 => {
                forged["reachable_functions"][predicate]["body"][0]["callee"]["span"]["file"] =
                    "types.h".into()
            }
            4 => {
                forged["reachable_functions"][predicate]["body"][0]["span"]["file"] =
                    "unlocked.h".into()
            }
            5 => {
                forged["reachable_functions"][read]["return_type"]["source_aliases"][0]["span"]["file"] =
                    "unlocked.h".into()
            }
            6 => {
                forged["reachable_functions"][predicate]["body"][0]["callee"]["declaration_id"] =
                    "missing".into()
            }
            7 => forged["dependencies"] = serde_json::json!(["types.h"]),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&forged_lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{mutation}: {error}");
    }
}

#[test]
fn locked_header_graph_requires_explicit_dependencies_and_fresh_bytes() {
    let project = header_graph_project("choose");
    let original = fs::read_to_string(project.directory.join("helpers.h")).unwrap();
    refresh_import(&project.config()).unwrap();
    let identity = load_import(&project.config())
        .unwrap()
        .identity()
        .to_string();
    fs::write(
        project.directory.join("helpers.h"),
        format!("{original}\n// changed\n"),
    )
    .unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(
        error.contains("dependencies differ")
            || error.contains("preprocessor")
            || error.contains("dependency"),
        "{error}"
    );
    refresh_import(&project.config()).unwrap();
    assert_ne!(identity, load_import(&project.config()).unwrap().identity());

    let mut missing = header_graph_project("choose");
    missing.dependencies.retain(|path| path != "helpers.h");
    missing.write_config("choose");
    let error = refresh_import(&missing.config()).unwrap_err();
    assert!(error.contains("configured dependencies"), "{error}");
    assert!(!missing.artifact().exists());
    assert!(!missing.lock().exists());
}

#[test]
fn locked_header_graph_validates_reachable_bodies_and_refuses_recursion() {
    for (body, diagnostic) in [
        (
            "for (; state.value != 0;) {} return 0;",
            "unsupported statement",
        ),
        ("return Read(state);", "recursive C++ calls"),
    ] {
        let project = header_graph_project("choose");
        let original = fs::read_to_string(project.directory.join("helpers.h")).unwrap();
        fs::write(
            project.directory.join("helpers.h"),
            original.replace("return state.value;", body),
        )
        .unwrap();
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(error.len() < 8000);
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn locked_header_graph_preserves_scalar_exception_contracts_offline() {
    let mut project = Project::with_fixture(
        "header-exception.cpp",
        "choose",
        "#include \"predicate.h\"\nint choose(bool fail) { if (predicate(fail)) { return 5; } else { return 6; } }",
    );
    fs::write(
        project.directory.join("predicate.h"),
        "#pragma once\nbool predicate(bool fail) { if (fail) { throw 7; } return true; }\n",
    )
    .unwrap();
    project.dependencies.push("predicate.h".into());
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(
        "choose",
        "header-exception.cpp",
        true,
        "scalar_int32",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(
        import.export().reachable_functions[0].span.file,
        "predicate.h"
    );
    fs::remove_file(&project.exporter).unwrap();
    let sidecar = r#"verifying "header-exception.cpp";
    bool predicate(bool fail) throws int32 { ensures result == true; exceptional ensures exception == 7; }
    int32 choose(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
    "#;
    check_selected_claim_certificate(&project, &import, sidecar);
    let (before, after) = sidecar
        .rsplit_once("exceptional ensures exception == 7;")
        .expect("caller has an exceptional postcondition");
    let hostile = format!("{before}exceptional ensures exception == 8;{after}");
    assert_ne!(hostile, sidecar);
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn locked_header_graph_can_call_back_into_the_selected_source() {
    let mut project = Project::with_fixture(
        "callback.cpp",
        "choose",
        "int callback(int value) noexcept;\n#include \"bridge.h\"\nint callback(int value) noexcept { return value; }\nint choose(int value) noexcept { return bridge(value); }\n",
    );
    fs::write(
        project.directory.join("bridge.h"),
        "#pragma once\ninline int bridge(int value) noexcept { return callback(value); }\n",
    )
    .unwrap();
    project.dependencies.push("bridge.h".into());
    project.write_config("choose");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().reachable_functions[0].span.file, "bridge.h");
    assert_eq!(
        import.export().reachable_functions[1].span.file,
        "callback.cpp"
    );
    fs::remove_file(&project.exporter).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "callback.cpp";
    int32 callback(int32 value) { ensures result == value; }
    int32 bridge(int32 value) { ensures result == value; }
    int32 choose(int32 value) { ensures result == value; }
    "#,
    );
}

#[test]
fn locked_header_graph_verifies_concrete_template_instances_only() {
    let mut project = Project::with_fixture(
        "template-graph.cpp",
        "choose",
        "#include \"templates.h\"\nint choose(int value) noexcept { return identity<int>(value); }",
    );
    fs::write(project.directory.join("templates.h"), "#pragma once\ntemplate<typename T> T identity(T value) noexcept { return value; }\ninline int unused(int value) noexcept { while (value != 0) {} return 0; }\n").unwrap();
    project.dependencies.push("templates.h".into());
    project.write_config("choose");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [callee] = import.export().reachable_functions.as_slice() else {
        panic!("only one instantiated callee is reachable")
    };
    assert_eq!(callee.span.file, "templates.h");
    fs::remove_file(&project.exporter).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        &format!(
            r#"verifying "template-graph.cpp";
    int32 {}(int32 value) {{ ensures result == value; }}
    int32 choose(int32 value) {{ ensures result == value; }}
    "#,
            cpp_spelling(&import, &callee.declaration_id)
        ),
    );
}

#[test]
fn locked_header_graph_retains_object_constant_and_undeclared_macro_boundaries() {
    for (header, diagnostic) in [
        (
            "inline constexpr int value = 7; inline int read() noexcept { return value; }",
            "constants must have const signed or unsigned 64-bit type",
        ),
        (
            "struct Guard { int value; explicit Guard(int initial) noexcept : value(initial) {} ~Guard() noexcept { value = 0; } }; inline int read() noexcept { Guard guard(0); return 0; }",
            "selected file",
        ),
        (
            "#include \"macro.h\"\ninline int read() noexcept { return VALUE; }",
            "differ from configured dependencies",
        ),
    ] {
        let mut project = Project::with_fixture(
            "bounded-header.cpp",
            "choose",
            "#include \"bounded.h\"\nint choose() noexcept { return read(); }",
        );
        fs::write(project.directory.join("bounded.h"), header).unwrap();
        fs::write(project.directory.join("macro.h"), "#define VALUE 7\n").unwrap();
        project.dependencies.push("bounded.h".into());
        project.write_config("choose");
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(error.len() < 8000);
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
fn converted_call_initializers_preserve_aliases_and_header_contracts_offline() {
    let mut project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "#include \"converted.h\"\nAmount relay(Amount value) noexcept { Amount captured = Amount(echo(value)); return captured; }",
    );
    fs::write(project.directory.join("converted.h"), "#pragma once\nusing Amount = long; inline Amount echo(Amount value) noexcept { return value; }").unwrap();
    project.dependencies.push("converted.h".into());
    project.write_config("relay");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let cast = &artifact["functions"][0]["body"][0]["initializer"]["conversions"][0];
    assert_eq!(cast["cast_kind"], "no_op");
    assert_eq!(cast["explicit"], true);
    assert_eq!(cast["span"]["file"], "converted.cpp");
    assert_eq!(
        cast["value_type"]["source_aliases"][0]["span"]["file"],
        "converted.h"
    );
    fs::remove_file(&project.exporter).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "converted.cpp";
int64 echo(int64 value) { ensures result == value; }
int64 relay(int64 value) { ensures result == value; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn converted_call_initializers_preserve_modulo_narrowing_and_reject_false_fit() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "unsigned long echo(unsigned long value) noexcept { return value; } int relay(unsigned long value) noexcept { int captured = static_cast<int>(echo(value)); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "converted.cpp";
uint64 echo(uint64 value) { ensures result == value; }
int32 relay(uint64 value) { requires value == 18446744073709551615u64; ensures result == -1; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let hostile = source.replace(
        "ensures result == -1",
        "ensures to_integer(result) == to_integer(value)",
    );
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn converted_call_initializers_keep_implicit_and_boolean_conversion_order() {
    for (body, expected, kinds) in [
        (
            "long captured = echo(value);",
            "value",
            vec!["integral_cast"],
        ),
        (
            "long captured = static_cast<bool>(echo(value));",
            "1i64",
            vec!["integral_to_boolean", "no_op", "integral_cast"],
        ),
    ] {
        let project = Project::with_fixture(
            "converted.cpp",
            "relay",
            &format!(
                "int echo(int value) noexcept {{ return value; }} long relay(int value) noexcept {{ {body} return captured; }}"
            ),
        );
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let conversions = artifact["functions"][0]["body"][0]["initializer"]["conversions"]
            .as_array()
            .unwrap();
        assert_eq!(
            conversions
                .iter()
                .map(|cast| cast["cast_kind"].as_str().unwrap())
                .collect::<Vec<_>>(),
            kinds
        );
        assert_eq!(conversions.last().unwrap()["explicit"], false);
        check_selected_claim_certificate(
            &project,
            &import,
            &format!(
                r#"verifying "converted.cpp";
int32 echo(int32 value) {{ ensures result == value; }}
int64 relay(int32 value) {{ requires value == 7; ensures result == {expected}; }}
"#
            ),
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn converted_call_initializers_evaluate_mutators_once_and_frame_siblings() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "struct Box { int value; int sibling; }; int bump(Box& box) noexcept { box.value = box.value + 1; return box.value; } long relay(Box& box) noexcept { long captured = static_cast<long>(bump(box)); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "converted.cpp";
int32 bump(struct Box& box) { owns box.value; requires box.value == 0; ensures box.value == 1; ensures result == 1; }
int64 relay(struct Box& box) { owns box.value; views box.sibling; requires box.value == 0; ensures box.value == 1; ensures result == 1i64; ensures box.sibling == old(box.sibling); }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let hostile = source.replace("owns box.value; views", "views box.value; views");
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn converted_call_initializers_reject_forged_conversion_types_kinds_and_origins() {
    use sha2::{Digest, Sha256};
    let mut project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "#include \"converted.h\"\nint relay(Amount value) noexcept { int captured = static_cast<int>(echo(value)); return captured; }",
    );
    fs::write(project.directory.join("converted.h"), "#pragma once\nusing Amount = long; inline Amount echo(Amount value) noexcept { return value; }").unwrap();
    project.dependencies.push("converted.h".into());
    project.write_config("relay");
    refresh_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..8 {
        let mut forged = artifact.clone();
        let cast = &mut forged["functions"][0]["body"][0]["initializer"]["conversions"][0];
        match mutation {
            0 => cast["source_type"]["bits"] = 32.into(),
            1 => cast["value_type"]["bits"] = 64.into(),
            2 => cast["cast_kind"] = "integral_to_boolean".into(),
            3 => cast["span"]["file"] = "converted.h".into(),
            4 => cast["source_type"]["source_aliases"][0]["span"]["file"] = "unlocked.h".into(),
            5 => cast["source_type"]["is_const"] = true.into(),
            6 => cast["cast_kind"] = "reinterpret_cast".into(),
            7 => cast["source_type"]["bits"] = 128.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&forged_lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{mutation}: {error}");
    }
}

#[test]
fn converted_call_initializers_keep_composed_effects_and_brace_narrowing_unsupported() {
    for source in [
        "int echo(int value) noexcept { return value; } int relay(int value) noexcept { int captured = echo(value) + 1; return captured; }",
        "long echo(long value) noexcept { return value; } int relay(long value) noexcept { int captured{echo(value)}; return captured; }",
    ] {
        let project = Project::with_fixture("converted.cpp", "relay", source);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000);
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
fn converted_call_initializers_emit_active_guard_cleanup_before_rethrow() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "struct Guard { int* slot; explicit Guard(int* value) noexcept : slot(value) { *slot = 1; } ~Guard() noexcept { *slot = 2; } }; int helper(bool fail) { if (fail) { throw 7; } return 5; } int relay(int* slot, bool fail) { Guard guard(slot); long captured = static_cast<long>(helper(fail)); return 5; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "converted.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let lowered = lower_import(&load_import(&project.config()).unwrap()).unwrap();
    fn has_cleanup(statement: &ProgramStatement) -> bool {
        match statement {
            ProgramStatement::Seq(statements) => {
                statements.iter().any(|statement| has_cleanup(statement))
            }
            ProgramStatement::UnwindCleanup { body, cleanup } => {
                contains_call(body, "helper") && contains_call(cleanup, "Guard::~Guard")
            }
            _ => false,
        }
    }
    assert!(has_cleanup(lowered.kernel_function().body()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn converted_call_initializers_preserve_scalar_exception_contracts_offline() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "int helper(bool fail) { if (fail) { throw 7; } return 5; } long relay(bool fail) { long captured = static_cast<long>(helper(fail)); return captured; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "converted.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let source = r#"verifying "converted.cpp";
int32 helper(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
int64 relay(bool fail) throws int32 { ensures result == 5i64; exceptional ensures exception == 7; }
"#;
    check_return_call_sidecar(&project, &import, source);
    let (before, after) = source
        .rsplit_once("exceptional ensures exception == 7;")
        .expect("caller has an exceptional postcondition");
    let hostile = format!("{before}exceptional ensures exception == 8;{after}");
    assert_ne!(hostile, source);
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn converted_call_initializers_keep_source_overflow_before_widening() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "int next(int value) noexcept { return value + 1; } long relay(int value) noexcept { long captured = static_cast<long>(next(value)); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "converted.cpp";
int32 next(int32 value) { requires value == 7; ensures result == 8; }
int64 relay(int32 value) { requires value == 7; ensures result == 8i64; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let hostile = source
        .replace("value == 7", "value == 2147483647")
        .replace("result == 8;", "result == -2147483648;")
        .replace("result == 8i64", "result == -2147483648i64");
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn converted_call_initializers_preserve_boolean_results() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "bool echo(bool value) noexcept { return value; } int relay(bool value) noexcept { int captured = static_cast<int>(echo(value)); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "converted.cpp";
bool echo(bool value) { ensures result == value; }
int32 relay(bool value) { requires value == true; ensures result == 1; }
"#,
    );
}

#[test]
fn converted_return_calls_preserve_implicit_widening_and_original_refused_source() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int echo(int value) noexcept { return value; } long relay(int value) noexcept { return echo(value); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; }
int64 relay(int32 value) { ensures result == value; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2s in the parallel gate"]
fn converted_return_calls_preserve_modulo_boolean_and_ordered_chains() {
    for (cpp_type, proof_type, result_type, body, requirement, expected) in [
        (
            "unsigned long",
            "uint64",
            "int32",
            "static_cast<int>(echo(value))",
            "value == 18446744073709551615u64",
            "-1",
        ),
        (
            "long",
            "int64",
            "bool",
            "static_cast<bool>(echo(value))",
            "value == 4294967296i64",
            "true",
        ),
        (
            "bool",
            "bool",
            "uint64",
            "static_cast<unsigned long>(echo(value))",
            "value == true",
            "1u64",
        ),
        (
            "long",
            "int64",
            "int64",
            "static_cast<long>(static_cast<unsigned>(echo(value)))",
            "value == 4294967297i64",
            "1i64",
        ),
    ] {
        let result_cpp = match result_type {
            "int32" => "int",
            "bool" => "bool",
            "uint64" => "unsigned long",
            _ => "long",
        };
        let project = Project::with_fixture(
            "relay.cpp",
            "relay",
            &format!(
                "{cpp_type} echo({cpp_type} value) noexcept {{ return value; }} {result_cpp} relay({cpp_type} value) noexcept {{ return {body}; }}"
            ),
        );
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            r#"verifying "relay.cpp";
{proof_type} echo({proof_type} value) {{ ensures result == value; }}
{result_type} relay({proof_type} value) {{ requires {requirement}; ensures result == {expected}; }}
"#
        );
        check_selected_claim_certificate(&project, &import, &source);
        let hostile = source.replace(
            &format!("ensures result == {expected}"),
            &format!(
                "ensures result == {}",
                if result_type == "bool" { "false" } else { "0" }
            ),
        );
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
        if proof_type == "uint64" {
            let false_fit = source.replace(
                &format!("ensures result == {expected}"),
                "ensures to_integer(result) == to_integer(value)",
            );
            fs::write(&path, &false_fit).unwrap();
            assert!(
                verify_program_prepared_project(
                    &read_click_project(&path, &false_fit).unwrap(),
                    &import,
                )
                .is_err()
            );
        }
    }
}

#[test]
fn converted_return_calls_preserve_locked_header_aliases_offline() {
    let mut project = Project::with_fixture(
        "relay.cpp",
        "relay",
        r#"#include "relay.h"
Amount relay(Amount value) noexcept { return Amount(echo(value)); }"#,
    );
    fs::write(
        project.directory.join("relay.h"),
        "#pragma once
using Amount = long; inline Amount echo(Amount value) noexcept { return value; }",
    )
    .unwrap();
    project.dependencies.push("relay.h".into());
    project.write_config("relay");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let cast = &artifact["functions"][0]["body"][0]["conversions"][0];
    assert_eq!(cast["cast_kind"], "no_op");
    assert_eq!(cast["explicit"], true);
    assert_eq!(cast["span"]["file"], "relay.cpp");
    assert_eq!(
        cast["value_type"]["source_aliases"][0]["span"]["file"],
        "relay.h"
    );
    fs::remove_file(&project.exporter).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        r#"verifying "relay.cpp";
int64 echo(int64 value) { ensures result == value; }
int64 relay(int64 value) { ensures result == value; }
"#,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn converted_return_calls_capture_converted_results_before_destructors() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        r#"
struct Restore {
 int* p; int saved;
 explicit Restore(int* slot) noexcept : p(slot), saved(*slot) { *p = 7; }
 ~Restore() noexcept { *p = saved; }
};
long read(int* slot) noexcept { return static_cast<long>(*slot) + 4294967296L; }
int relay(int& value) noexcept { Restore guard(&value); return static_cast<int>(read(&value)); }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let source = r#"verifying "relay.cpp";
Restore::Restore(int32* slot) {
 owns this->p; owns this->saved; owns slot[0..1];
 ensures this->p == slot; ensures this->saved == old(slot[0]); ensures slot[0] == 7;
 ensures separate(memory(*this), memory(this->p[0..1]));
}
Restore::~Restore() {
 requires separate(memory(*this), memory(this->p[0..1]));
 owns this->p; owns this->saved; owns this->p[0..1];
 ensures this->p == old(this->p); ensures this->saved == old(this->saved);
 ensures this->p[0] == old(this->saved);
}
int64 read(int32* slot) {
 views slot[0..1]; requires slot[0] == 7; ensures result == 4294967303i64;
 ensures slot[0] == old(slot[0]);
}
int32 relay(int32& value) {
 owns value; ensures result == 7; ensures value == old(value);
}
"#;
    check_selected_claim_certificate(&project, &import, source);
    for hostile in [
        source.replace("ensures result == 7;", "ensures result == 0;"),
        source.replace("ensures value == old(value);", "ensures value == 7;"),
    ] {
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn converted_return_calls_evaluate_mutators_once_and_preserve_sibling_authority() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "struct Box { int value; int sibling; }; long bump(Box& box) noexcept { box.value = box.value + 1; return box.value; } int relay(Box& box) noexcept { return static_cast<int>(bump(box)); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int64 bump(struct Box& box) { owns box.value; requires box.value == 0; ensures box.value == 1; ensures result == 1i64; }
int32 relay(struct Box& box) { owns box.value; views box.sibling; requires box.value == 0; ensures box.value == 1; ensures result == 1; ensures box.sibling == old(box.sibling); }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let hostile = source.replace("owns box.value; views", "views box.value; views");
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn converted_return_calls_preserve_scalar_exceptions_offline() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int helper(bool fail) { if (fail) { throw 7; } return 5; } long relay(bool fail) { return static_cast<long>(helper(fail)); }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "relay.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let source = r#"verifying "relay.cpp";
int32 helper(bool fail) throws int32 { ensures result == 5; exceptional ensures exception == 7; }
int64 relay(bool fail) throws int32 { ensures result == 5i64; exceptional ensures exception == 7; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let (before, after) = source
        .rsplit_once("exceptional ensures exception == 7;")
        .expect("caller has an exceptional postcondition");
    let hostile = format!("{before}exceptional ensures exception == 8;{after}");
    assert_ne!(hostile, source);
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn converted_return_calls_reject_forged_cast_chains_and_source_origins() {
    use sha2::{Digest, Sha256};
    let mut project = Project::with_fixture(
        "relay.cpp",
        "relay",
        r#"#include "relay.h"
int relay(Amount value) noexcept { return static_cast<int>(echo(value)); }"#,
    );
    fs::write(
        project.directory.join("relay.h"),
        "#pragma once
using Amount = long; inline Amount echo(Amount value) noexcept { return value; }",
    )
    .unwrap();
    project.dependencies.push("relay.h".into());
    project.write_config("relay");
    refresh_import(&project.config()).unwrap();
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..9 {
        let mut forged = artifact.clone();
        let returned = &mut forged["functions"][0]["body"][0];
        match mutation {
            0 => returned["conversions"][0]["source_type"]["bits"] = 32.into(),
            1 => returned["conversions"][0]["value_type"]["bits"] = 64.into(),
            2 => returned["conversions"][0]["cast_kind"] = "integral_to_boolean".into(),
            3 => returned["conversions"][0]["span"]["file"] = "relay.h".into(),
            4 => {
                returned["conversions"][0]["source_type"]["source_aliases"][0]["span"]["file"] =
                    "unlocked.h".into()
            }
            5 => returned["conversions"][0]["source_type"]["is_const"] = true.into(),
            6 => returned["conversions"] = serde_json::json!([]),
            7 => returned["value_type"]["bits"] = 64.into(),
            8 => returned["conversions"][0]["source_type"]["bits"] = 128.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&forged_lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{mutation}: {error}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn converted_return_expression_observers_verify_composed_values() {
    for (body, result) in [
        ("static_cast<int>(echo(value) + 1)", 1),
        ("echo(value) + echo(value)", 0),
    ] {
        let source = format!(
            "int echo(int value) noexcept {{ return value; }} int relay(int value) noexcept {{ return {body}; }}"
        );
        let project = Project::with_fixture("relay.cpp", "relay", &source);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = format!(
            r#"verifying "relay.cpp";
int32 echo(int32 value) {{ ensures result == value; }}
int32 relay(int32 value) {{ requires value == 0; ensures result == {result}; }}
"#
        );
        check_first_claim_certificate(&project, &import, &sidecar);
    }
}

#[test]
fn converted_return_calls_and_initializers_bound_exported_conversion_chains() {
    for body in [
        format!("return {}echo();", "(int)".repeat(257)),
        format!(
            "int captured = {}echo(); return captured;",
            "(int)".repeat(257)
        ),
    ] {
        let project = Project::with_fixture(
            "relay.cpp",
            "relay",
            &format!("int echo() noexcept {{ return 7; }} int relay() noexcept {{ {body} }}"),
        );
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains("scalar call-result conversions"), "{error}");
        assert!(error.len() < 8000);
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
fn converted_return_calls_emit_active_object_cleanup_on_exception() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "struct Guard { int* slot; explicit Guard(int* value) noexcept : slot(value) { *slot = 1; } ~Guard() noexcept { *slot = 2; } }; int helper(bool fail) { if (fail) { throw 7; } return 5; } long relay(int* slot, bool fail) { Guard guard(slot); return static_cast<long>(helper(fail)); }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "relay.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let lowered = lower_import(&load_import(&project.config()).unwrap()).unwrap();
    fn has_cleanup(statement: &ProgramStatement) -> bool {
        match statement {
            ProgramStatement::Seq(statements) => {
                statements.iter().any(|statement| has_cleanup(statement))
            }
            ProgramStatement::UnwindCleanup { body, cleanup } => {
                contains_call(body, "helper") && contains_call(cleanup, "Guard::~Guard")
            }
            _ => false,
        }
    }
    assert!(has_cleanup(lowered.kernel_function().body()));
}

#[test]
fn converted_return_calls_keep_source_overflow_before_widening() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int next(int value) noexcept { return value + 1; } long relay(int value) noexcept { return static_cast<long>(next(value)); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 next(int32 value) { requires value == 7; ensures result == 8; }
int64 relay(int32 value) { requires value == 7; ensures result == 8i64; }
"#;
    check_selected_claim_certificate(&project, &import, source);
    let hostile = source
        .replace("value == 7", "value == 2147483647")
        .replace("result == 8;", "result == -2147483648;")
        .replace("result == 8i64", "result == -2147483648i64");
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn execution_theorem_proof_retains_struct_argument_field_metadata() {
    let project = Project::with_fixture(
        "read.cpp",
        "read",
        "struct Child { int value; }; struct State { long sibling; Child child; }; int read(const State& state) noexcept { return state.child.value; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "read.cpp";
int32 read(const struct State& state) {
    views state.child.value;
    ensures result == state.child.value;
}
contract int32 PositiveRead(const struct State& state) {
    views state.child.value;
    requires state.child.value == 2;
    ensures result == 2;
}
theorem read_application() executes read(const struct State& state) {
    ensures PositiveRead(&read) by {
        have state.child.value > 0 by { close() using { state.child.value == 2; } }
        step_until(function.exit); close();
    }
}
"#;
    let path = project.directory.join("read.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    let sites =
        project_smart_tactic_source_sites(&parsed, &ProgramInputs::program(&import)).unwrap();
    let first = sites
        .iter()
        .find(|site| site.claim_label.starts_with("read_application."))
        .unwrap();
    let position = project_tactic_source_position(
        &parsed,
        &ProgramInputs::program(&import),
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &parsed,
        &ProgramInputs::program(&import),
        position.line,
        position.column,
    )
    .unwrap();
    let rewritten = parsed.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    // Session construction cold-verifies this complete program once.
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
    let position = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(&import),
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .unwrap();
    let path = project.directory.join("hostile.click");
    let hostile = source.replace("requires state.child.value == 2;", "");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
    let (definitions, application) = source.split_once("theorem read_application()").unwrap();
    let wrong_field = format!(
        "{definitions}theorem read_application(){}",
        application.replace("child.value", "child.missing")
    );
    fs::write(&path, &wrong_field).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, &wrong_field).unwrap(), &import)
            .unwrap_err();
    assert!(error.message().len() < 8000);
}

fn check_converted_wide_call_results(initializer: bool) {
    for (cpp_source, source, cpp_result, result, lo, hi) in [
        (
            "__int128",
            "int128",
            "long",
            "int64",
            "-9223372036854775808",
            "9223372036854775807",
        ),
        (
            "__int128",
            "int128",
            "int",
            "int32",
            "-2147483648",
            "2147483647",
        ),
        (
            "__int128",
            "int128",
            "unsigned long",
            "uint64",
            "0",
            "18446744073709551615",
        ),
        (
            "__int128",
            "int128",
            "unsigned",
            "uint32",
            "0",
            "4294967295",
        ),
        (
            "unsigned __int128",
            "uint128",
            "long",
            "int64",
            "0",
            "9223372036854775807",
        ),
        (
            "unsigned __int128",
            "uint128",
            "int",
            "int32",
            "0",
            "2147483647",
        ),
        (
            "unsigned __int128",
            "uint128",
            "unsigned long",
            "uint64",
            "0",
            "18446744073709551615",
        ),
        (
            "unsigned __int128",
            "uint128",
            "unsigned",
            "uint32",
            "0",
            "4294967295",
        ),
    ] {
        let body = if initializer {
            format!(
                "{cpp_result} narrowed = static_cast<{cpp_result}>(echo(value)); return narrowed;"
            )
        } else {
            format!("return static_cast<{cpp_result}>(echo(value));")
        };
        let project = Project::with_fixture(
            "wide.cpp",
            "relay",
            &format!(
                "{cpp_source} echo({cpp_source} value) noexcept {{ return value; }} {cpp_result} relay({cpp_source} value) noexcept {{ {body} }}"
            ),
        );
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let cert = cast_identity_proof("to_integer(captured)", lo, hi);
        let proof = format!(
            r#"verifying "wide.cpp";
{source} echo({source} value) {{ ensures result == value; }}
{result} relay({source} value) {{
 requires {lo} <= to_integer(value); requires to_integer(value) <= {hi};
 ensures to_integer(result) == to_integer(value);
}} by {{
 step_until(call(0).entry);
 let {{ result: captured }} = step(echo, {{}});
 have {lo} <= to_integer(captured) by {{ close() using {{ {lo} <= to_integer(value); to_integer(captured) == to_integer(value); }} }}
 have to_integer(captured) <= {hi} by {{ close() using {{ to_integer(value) <= {hi}; to_integer(captured) == to_integer(value); }} }}
 step_until(function.exit);
 have to_integer(result) == to_integer(captured) by {{ {cert} }}
 close() using {{ to_integer(result) == to_integer(captured); to_integer(captured) == to_integer(value); }}
}}
"#
        );
        check_selected_claim_certificate(&project, &import, &proof);
        if source == "int128" && result == "int64" {
            for hostile in [
                proof.replacen("ensures result == value;", "", 1),
                proof.replacen(
                    "ensures to_integer(result) == to_integer(value);",
                    "ensures to_integer(result) == to_integer(value) + 1;",
                    1,
                ),
            ] {
                let path = project.directory.join("hostile.click");
                fs::write(&path, &hostile).unwrap();
                let error = verify_program_prepared_project(
                    &read_click_project(&path, &hostile).unwrap(),
                    &import,
                )
                .unwrap_err();
                assert!(error.message().len() < 8000);
            }
        }
        // Each bound the narrowing needs is a requirement: without it the
        // value may not fit the result type. An unsigned source's lower
        // bound, `0 <= to_integer(value)`, is instead its type's own range,
        // so the proof holds without that requirement.
        let lower_is_the_type_range = source.starts_with('u');
        for (missing, needed) in [
            (
                format!("requires {lo} <= to_integer(value);"),
                !lower_is_the_type_range,
            ),
            (format!("requires to_integer(value) <= {hi};"), true),
        ] {
            let hostile = proof.replace(&missing, "");
            let path = project.directory.join("hostile.click");
            fs::write(&path, &hostile).unwrap();
            let verified = verify_program_prepared_project(
                &read_click_project(&path, &hostile).unwrap(),
                &import,
            );
            if needed {
                let error = verified.unwrap_err();
                assert!(error.message().len() < 8000);
            } else {
                verified.unwrap_or_else(|error| {
                    panic!(
                        "{source} -> {result}: `{missing}` is the source type's range: {}",
                        error.message()
                    )
                });
            }
        }
    }
}
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn converted_wide_return_calls_preserve_values_with_checked_destination_bounds() {
    check_converted_wide_call_results(false);
}
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn converted_wide_call_initializers_preserve_values_with_checked_destination_bounds() {
    check_converted_wide_call_results(true);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn converted_wide_boolean_calls_observe_high_bits() {
    for (point, answer) in [("0", "false"), ("18446744073709551616", "true")] {
        let project = Project::with_fixture(
            "wide.cpp",
            "relay",
            "unsigned __int128 echo(unsigned __int128 value) noexcept { return value; } bool relay(unsigned __int128 value) noexcept { return static_cast<bool>(echo(value)); }",
        );
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let zero_fact = if answer == "false" {
            String::new()
        } else {
            format!(
                "have not (to_integer(captured) == 0) by {{ rewrite(to_integer(captured), {point}); normalize(); }}"
            )
        };
        let proof = format!(
            r#"verifying "wide.cpp";
uint128 echo(uint128 value) {{ ensures result == value; }}
bool relay(uint128 value) {{ requires to_integer(value) == {point}; ensures result == {answer}; }} by {{
 step_until(call(0).entry);
 let {{ result: captured }} = step(echo, {{}});
 have to_integer(captured) == {point} by {{ close() using {{ to_integer(value) == {point}; to_integer(captured) == to_integer(value); }} }}
 {zero_fact}
 step_until(function.exit); close();
}}
"#
        );
        check_selected_claim_certificate(&project, &import, &proof);
        let hostile = proof.replace(
            &format!("ensures result == {answer};"),
            &format!(
                "ensures result == {};",
                if answer == "false" { "true" } else { "false" }
            ),
        );
        let path = project.directory.join("hostile.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
fn cpp_pointer_returns_preserve_identity_and_modular_results_offline() {
    let project = Project::with_fixture(
        "return.cpp",
        "run",
        "int* identity(int* data) noexcept { return data; }\nint* run(int* data) noexcept { return identity(data); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "return.cpp";
int32* identity(int32* data) { ensures result == data; }
int32* run(int32* data) { ensures result == data; }
"#;
    check_first_claim_certificate(&project, &import, sidecar);
    let hostile = sidecar.replace("ensures result == data; }", "ensures result == data + 1; }");
    assert_ne!(hostile, sidecar);
    let path = project.directory.join("bad.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
    let reference_sidecar = sidecar.replace("int32* identity", "int32& identity");
    fs::write(&path, &reference_sidecar).unwrap();
    assert!(
        verify_program_prepared_project(
            &read_click_project(&path, &reference_sidecar).unwrap(),
            &import
        )
        .is_err()
    );
    // Recompute the lock so these exercise semantic validation, not only hashes.
    use sha2::{Digest, Sha256};
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        match mutation {
            0 => forged["functions"][0]["return_type"]["pointee"]["bits"] = 64.into(),
            1 => forged["functions"][0]["return_type"]["pointee"]["is_const"] = true.into(),
            2 => forged["functions"][0]["body"][0]["value_type"]["pointee"]["bits"] = 64.into(),
            3 => forged["reachable_functions"][0]["return_type"]["pointee"]["bits"] = 64.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.contains("C++"), "{error}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn cpp_native_reference_results_preserve_aliases_and_require_backing_authority_offline() {
    let project = Project::with_fixture(
        "return.cpp",
        "run",
        "int& identity(int& value) noexcept { return value; }\nint& run(int& value) noexcept { return identity(value); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let aliases = r#"verifying "return.cpp";
int32& identity(int32& value) { ensures &result == &value; }
int32& run(int32& value) { ensures &result == &value; }
"#;
    check_first_claim_certificate(&project, &import, aliases);
    let values = aliases.replace(
        "{ ensures &result == &value; }",
        "{ owns value; ensures &result == &value; ensures result == old(value); }",
    );
    check_first_claim_certificate(&project, &import, &values);
    check_first_claim_certificate(
        &project,
        &import,
        &values.replace("owns value;", "views value;"),
    );
    for hostile in [
        aliases.replace(
            "ensures &result == &value;",
            "ensures &result == &value + 1;",
        ),
        aliases.replace("ensures &result == &value;", "ensures result == 0;"),
        aliases.replace("int32& identity", "int32* identity"),
        aliases.replace(
            "ensures &result == &value;",
            "ensures old(&result) == &value;",
        ),
        values.replace(
            "ensures result == old(value);",
            "ensures result != old(value);",
        ),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&parsed, &import).is_err(),
            "{hostile}"
        );
    }
    use sha2::{Digest, Sha256};
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..5 {
        let mut forged = artifact.clone();
        match mutation {
            0 => forged["functions"][0]["return_type"]["kind"] = "pointer".into(),
            1 => forged["functions"][0]["body"][0]["value_type"]["pointee"]["bits"] = 64.into(),
            2 => {
                forged["reachable_functions"][0]["body"][0]["value"]["address"]["kind"] =
                    "load".into()
            }
            3 => {
                forged["reachable_functions"][0]["body"][0]["value"]["value_type"]["pointee"]["bits"] =
                    64.into()
            }
            4 => {
                forged["reachable_functions"][0]["return_type"]["pointee"]["is_const"] = true.into()
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "accepted mutation {mutation}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn cpp_reference_results_bind_live_pointer_referents_without_loading() {
    let project = Project::with_fixture(
        "return.cpp",
        "run",
        "int& run(int* data) noexcept { return *data; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let aliases = r#"verifying "return.cpp";
int32& run(int32* data) { views data[0..1]; ensures &result == data; }
"#;
    check_first_claim_certificate(&project, &import, aliases);
    let values = aliases.replace(
        "ensures &result == data;",
        "ensures &result == data; ensures result == old(data[0]);",
    );
    check_first_claim_certificate(&project, &import, &values);
    for hostile in [
        aliases.replace("views data[0..1];", ""),
        aliases.replace("ensures &result == data;", "ensures &result == data + 1;"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn cpp_reference_locals_preserve_aliases_and_modular_call_results_offline() {
    let project = Project::with_fixture(
        "local.cpp",
        "run",
        "int& helper(int& value) noexcept { int& alias = value; return alias; }\nint& run(int& value) noexcept { int& back = helper(value); back = 9; return back; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "local.cpp";
int32& helper(int32& value) { ensures &result == &value; }
int32& run(int32& value) { owns value; ensures &result == &value; ensures result == 9; ensures value == 9; }
"#;
    check_first_claim_certificate(&project, &import, sidecar);
    for hostile in [
        sidecar.replace("owns value;", "views value;"),
        sidecar.replace("owns value;", ""),
        sidecar.replace("ensures result == 9;", "ensures result == 10;"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
    }
}

/// A proof names a reference local as it names a reference parameter: the
/// name is the referent, and `&name` is its address.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn cpp_reference_locals_read_as_their_referents_in_a_proof_offline() {
    let project = Project::with_fixture(
        "local.cpp",
        "run",
        "int run(int& value) noexcept { int& r = value; r = 1; return r; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "local.cpp";
int32 run(int32& value) { owns value; ensures result == 1; ensures value == 1; } by {
    PROOF
}
"#;
    let proof = |body: &str| sidecar.replace("PROOF", body);
    check_first_claim_certificate(
        &project,
        &import,
        &proof(
            "step(); step(); step(); have r == 1; have &r == &value; step_until(function.exit); close();",
        ),
    );
    for (body, expected) in [
        (
            "step(); step(); step(); have r == 2; step_until(function.exit); close();",
            "r == 2",
        ),
        (
            "step(); step(); step(); have r[0] == 1; step_until(function.exit); close();",
            "`r` is a reference and names the value it refers to, so it takes no index",
        ),
        (
            "step_until(assignment(r, 0).entry); step_until(function.exit); close();",
            "`r` is a reference, and binding a reference is not an assignment",
        ),
    ] {
        let hostile = proof(body);
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        let error =
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .expect_err("the proof misstates or misnames the reference local");
        assert!(
            error.message().contains(expected),
            "{body}: {}",
            error.message()
        );
    }
}

/// A failure's "C operation" line prints a read through a scalar reference
/// parameter as the sidecar writes it, `value`, not as the kernel term
/// `load<int32>(&value)`.
#[test]
fn cpp_scalar_reference_reads_print_as_referents_in_a_c_operation_offline() {
    let project = Project::with_fixture(
        "local.cpp",
        "read",
        "int read(int& value) noexcept { return value; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let text = "verifying \"local.cpp\";\nint32 read(int32& value) { ensures result == result; }\n";
    let path = project.directory.join("bad.click");
    fs::write(&path, text).unwrap();
    let error = verify_program_prepared_project(&read_click_project(&path, text).unwrap(), &import)
        .expect_err("the contract lacks the authority the function uses");
    assert!(
        error.message().contains("C operation: return value"),
        "{}",
        error.message()
    );
    assert!(
        !error.message().contains("load<int32>(&"),
        "{}",
        error.message()
    );
}

/// A read at the start of a struct referent prints as the field it is,
/// `c.first`, and the refusal names the referent's fields, because the
/// parameter carries its record's layout for presentation.
#[test]
fn cpp_struct_reference_reads_print_as_fields_in_a_c_operation_offline() {
    let project = Project::with_fixture(
        "local.cpp",
        "get",
        "struct cell { int first; int second; };\nint get(cell& c) noexcept { return c.first; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let text = "verifying \"local.cpp\";\nint32 get(struct cell& c) { views c.second; ensures result == result; }\n";
    let path = project.directory.join("bad.click");
    fs::write(&path, text).unwrap();
    let error = verify_program_prepared_project(&read_click_project(&path, text).unwrap(), &import)
        .expect_err("the contract views another field than the one the function reads");
    assert!(
        error.message().contains("C operation: return c.first"),
        "{}",
        error.message()
    );
    assert!(
        !error.message().contains("load<int32>(&"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.2s for C++ import, expansion, and cold replay"]
fn cpp_expansion_names_the_capture_by_its_call_result() {
    let project = Project::with_fixture(
        "capture.cpp",
        "pick",
        "int echo(int value) noexcept { return value; } int pick(int value) noexcept { if (echo(value) > 0) { return 1; } return 0; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let text = r#"verifying "capture.cpp";
int32 echo(int32 value) { requires value >= -100; ensures result >= -100; }
int32 pick(int32 value) { requires value >= -100; ensures result >= 0; }
"#;
    let path = project.directory.join("pick.click");
    fs::write(&path, text).unwrap();
    let parsed = read_click_project(&path, text).unwrap();
    let claim = "pick.ensures_0";
    let expanded = click::surface::expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        claim,
    )
    .unwrap_or_else(|error| panic!("{}", error.report()));
    assert!(expanded.contains("call(echo, 0).result"), "{expanded}");
    assert!(!expanded.contains(".temporary("), "{expanded}");
    click::surface::without_implicit_solve_for_claim(claim, || {
        verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
            .map(|_| ())
            .map_err(|error| error.report())
    })
    .unwrap();
}

/// `click expand` writes a branch condition over a scalar reference with the
/// bare name the sidecar uses, and the expansion verifies.
#[test]
fn cpp_expansion_writes_a_branch_over_a_reference_by_its_referent_offline() {
    let project = Project::with_fixture(
        "local.cpp",
        "pick",
        "int pick(int& value) noexcept { if (value > 0) { return 1; } return 0; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let text = "verifying \"local.cpp\";\nint32 pick(int32& value) { views value; ensures result >= 0; }\n";
    let path = project.directory.join("pick.click");
    fs::write(&path, text).unwrap();
    let parsed = read_click_project(&path, text).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
    let sites =
        project_smart_tactic_source_sites(&parsed, &ProgramInputs::program(&import)).unwrap();
    let first = sites.first().unwrap();
    let position = project_tactic_source_position(
        &parsed,
        &ProgramInputs::program(&import),
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &parsed,
        &ProgramInputs::program(&import),
        position.line,
        position.column,
    )
    .unwrap();
    assert!(!expanded.contains("load<int32>(&"), "{expanded}");
    verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

/// `click expand` writes a branch condition over a field of a struct
/// reference as the sidecar writes that field, and the expansion verifies.
#[test]
fn cpp_expansion_writes_a_branch_over_a_struct_reference_by_its_field_offline() {
    let project = Project::with_fixture(
        "local.cpp",
        "pick",
        "struct cell { int first; int second; };\nint pick(cell& c) noexcept { if (c.second > 0) { return 1; } return 0; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let text = "verifying \"local.cpp\";\nint32 pick(struct cell& c) { views c.second; ensures result >= 0; }\n";
    let path = project.directory.join("pick.click");
    fs::write(&path, text).unwrap();
    let parsed = read_click_project(&path, text).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
    let sites =
        project_smart_tactic_source_sites(&parsed, &ProgramInputs::program(&import)).unwrap();
    let first = sites.first().unwrap();
    let position = project_tactic_source_position(
        &parsed,
        &ProgramInputs::program(&import),
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &parsed,
        &ProgramInputs::program(&import),
        position.line,
        position.column,
    )
    .unwrap();
    assert!(
        expanded.contains("if at(region(0).entry, c.second) > "),
        "{expanded}"
    );
    assert!(!expanded.contains("load<int32>("), "{expanded}");
    verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn cpp_const_reference_locals_bind_pointer_storage_without_loading_offline() {
    let project = Project::with_fixture(
        "local.cpp",
        "run",
        "const int& run(int* data) noexcept { const int& back = *(data + 1); return back; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "local.cpp";
const int32& run(int32* data) { views data[0..2]; ensures &result == data + 1; ensures result == old(data[1]); }
"#;
    check_first_claim_certificate(&project, &import, sidecar);
    let hostile = sidecar.replace("views data[0..2];", "views data[0..1];");
    let path = project.directory.join("bad.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s for unknown-pointer fresh, expanded and retained checks"]
fn cpp_unknown_pointer_formation_requires_bounds_before_any_dereference() {
    let project = Project::with_fixture(
        "formation.cpp",
        "run",
        "int* run(int* data) noexcept { return data + 1; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "formation.cpp";
int32* run(int32* data) { ensures true; }
"#;
    let path = project.directory.join("bad.click");
    fs::write(&path, sidecar).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, sidecar).unwrap(), &import)
            .unwrap_err();
    assert!(error.to_string().contains("pointer arithmetic"), "{error}");
    check_arithmetic_sidecar(
        &project,
        &import,
        &sidecar.replace(
            "ensures true;",
            "views data[0..1]; ensures result == data + 1;",
        ),
    );
}

#[test]
fn cpp_reference_formation_rejects_one_past_even_under_trivial_postconditions() {
    let project = Project::with_fixture(
        "return.cpp",
        "run",
        "int& run(int* data) noexcept { return *(data + 1); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "return.cpp";
int32& run(int32* data) { views data[0..1]; ensures true; }
"#;
    let path = project.directory.join("bad.click");
    fs::write(&path, sidecar).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, sidecar).unwrap(), &import)
            .is_err()
    );
    check_first_claim_certificate(
        &project,
        &import,
        &sidecar
            .replace("views data[0..1];", "views data[0..2];")
            .replace("ensures true;", "ensures &result == data + 1;"),
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn cpp_const_reference_results_preserve_native_qualification_offline() {
    let project = Project::with_fixture(
        "return.cpp",
        "run",
        "const int& identity(const int& value) noexcept { return value; }\nconst int& run(const int& value) noexcept { return identity(value); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let aliases = r#"verifying "return.cpp";
const int32& identity(const int32& value) { ensures &result == &value; }
const int32& run(const int32& value) { ensures &result == &value; }
"#;
    check_first_claim_certificate(&project, &import, aliases);
    let values = aliases.replace(
        "{ ensures &result == &value; }",
        "{ views value; ensures &result == &value; ensures result == old(value); }",
    );
    check_first_claim_certificate(&project, &import, &values);
    let hostile = aliases.replace("const int32& identity(", "int32& identity(");
    let path = project.directory.join("bad.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn cpp_bounded_native_descriptor_last_reference_verifies_offline() {
    let project = Project::with_fixture(
        "bounds.cpp",
        "run",
        "struct View { int* data; unsigned long size; }; int& run(const View& view) noexcept { return *(view.data + (view.size - 1UL)); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    // The bound is the code's `unsigned long`, uncast, and the last
    // element is at `size - 1` in that type. Nothing bounds `size` from
    // above: the held range states its own span limit.
    let source = r#"verifying "bounds.cpp";
int32& run(const struct View& view) {
 views view.data;
 views view.size;
 views view.data[0..view.size];
 requires 1u64 <= view.size;
 ensures &result == view.data + (view.size - 1u64);
 ensures result == old(view.data[view.size - 1u64]);
}
 "#;
    check_first_claim_certificate(&project, &import, source);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn direct_subscript_methods_select_and_preserve_reference_authority_offline() {
    let cpp = "struct Cell { int* data; int& operator[](unsigned long index) noexcept { return *data; } }; int& probe(Cell& cell, unsigned long index) noexcept { return cell[index]; }";
    let method = r#"verifying "index.cpp";
int32& Cell::operator[](uint64 index) {
 views this->data;
 views this->data[0..1];
 ensures &result == this->data;
 ensures result == old(this->data[0]);
}
"#;
    let caller = r#"int32& probe(struct Cell& cell, uint64 index) {
 views cell.data;
 views cell.data[0..1];
 ensures &result == cell.data;
 ensures result == old(cell.data[0]);
}
"#;
    for selector in ["Cell::operator[]", "probe"] {
        let project = Project::with_fixture("index.cpp", selector, cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert!(
            import.export().functions[0].name == "Cell_operator_index"
                || import.export().functions[0].name == "probe"
        );
        let source = if selector == "probe" {
            format!("{method}{caller}")
        } else {
            method.to_owned()
        };
        let path = project.directory.join("index.click");
        fs::write(&path, &source).unwrap();
        let parsed = read_click_project(&path, &source).unwrap();
        verify_program_prepared_project(&parsed, &import).unwrap();
        for hostile in [
            source.replace(
                " views this->data;
 views this->data[0..1];",
                "",
            ),
            source.replace(
                " ensures &result == this->data;",
                " ensures &result == this->data + 1;",
            ),
        ] {
            assert!(
                verify_program_prepared_project(
                    &read_click_project(&path, &hostile).unwrap(),
                    &import
                )
                .is_err()
            );
        }
    }
    let unsupported = Project::with_fixture(
        "index.cpp",
        "probe",
        "struct Cell { int value; int operator+(int other) noexcept { return other; } }; int probe(Cell& cell) noexcept { return cell + 1; }",
    );
    let error = refresh_import(&unsupported.config()).unwrap_err();
    assert!(
        error.contains("operator+=, operator-= and operator[] only"),
        "{error}"
    );
    assert!(!unsupported.artifact().exists());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn cpp_external_backing_reference_survives_descriptor_destruction_offline() {
    check_cpp_descriptor_backing_lifetime(false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.4s in the parallel gate"]
fn cpp_external_backing_reference_remains_writable_after_descriptor_destruction_offline() {
    check_cpp_descriptor_backing_lifetime(true);
}

fn check_cpp_descriptor_backing_lifetime(writes: bool) {
    let harness = "struct View { int* data; explicit View(int* input) noexcept : data(input) {} ~View() noexcept { data = nullptr; } int& get() const noexcept { return *data; } }; int& run(int* data) noexcept { View view(data); return view.get(); }";
    let cpp = if writes {
        format!(
            "{harness} int write(int* data, int input) noexcept {{ int& element = run(data); element = input; return element; }}"
        )
    } else {
        harness.to_owned()
    };
    let project = Project::with_fixture("lifetime.cpp", if writes { "write" } else { "run" }, &cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "lifetime.cpp";
View::View(int32* input) {
 owns this->data;
 ensures this->data == input;
}
View::~View() {
 owns this->data;
}
int32& View::get() const {
 views this->data;
 views this->data[0..1];
 ensures &result == this->data;
 ensures result == old(this->data[0]);
}
int32& run(int32* data) {
 views data[0..1];
 ensures &result == data;
 ensures result == old(data[0]);
}
"#;
    let source = if writes {
        format!(
            "{source}{}",
            r#"
int32 write(int32* data, int32 input) {
 owns data[0..1];
 ensures result == input;
 ensures data[0] == input;
}
"#
        )
    } else {
        source.to_owned()
    };
    let source = source.as_str();
    check_selected_claim_certificate(&project, &import, source);
    let hostile = if writes {
        vec![
            source.replace(" owns data[0..1];", " views data[0..1];"),
            source.replace(
                " ensures data[0] == input;",
                " ensures data[0] == old(data[0]);",
            ),
        ]
    } else {
        vec![
            source.replace(" views data[0..1];", ""),
            source.replace(" ensures &result == data;", " ensures &result == data + 1;"),
        ]
    };
    for bad in hostile {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn cpp_literal_null_pointer_values_verify_without_storage_authority_offline() {
    for expression in [
        "nullptr",
        "0",
        "0UL",
        "static_cast<int*>(nullptr)",
        "static_cast<int*>(0)",
    ] {
        let cpp = format!("int* run() noexcept {{ return {expression}; }}");
        let project = Project::with_fixture("null.cpp", "run", &cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = r#"verifying "null.cpp";
int32* run() { ensures result == 0; }
"#;
        check_return_call_sidecar(&project, &import, source);
        let bad = source.replace("result == 0", "result != 0");
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
fn cpp_literal_null_pointer_dereference_requires_live_backing_offline() {
    let project = Project::with_fixture(
        "null.cpp",
        "run",
        "int read(int* data) noexcept { return *data; } int run() noexcept { return read(nullptr); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "null.cpp";
int32 read(int32* data) { views data[0..1]; ensures result == data[0]; }
int32 run() { ensures 1 == 1; }
"#;
    let path = project.directory.join("null.click");
    fs::write(&path, source).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, source).unwrap(), &import)
            .unwrap_err();
    assert!(error.message().contains("resource"), "{}", error.message());
}

#[test]
fn cpp_null_pointer_conversions_keep_effectful_operands_and_other_types_outside_profile() {
    for (cpp, message) in [
        (
            "decltype(nullptr) produce() noexcept { return nullptr; } int* run() noexcept { return produce(); }",
            "unsupported C++ call-result conversion",
        ),
        (
            "int* run() noexcept { return reinterpret_cast<int*>(1); }",
            "unsupported explicit C++ conversion",
        ),
        (
            "long long* run() noexcept { return nullptr; }",
            "native element pointer",
        ),
    ] {
        let project = Project::with_fixture("null.cpp", "run", cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(message), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn cpp_reference_into_destroyed_local_backing_cannot_be_read_offline() {
    let cpp = "struct Cell { int value; int state; explicit Cell(int input) noexcept : value(input), state(1) {} ~Cell() noexcept { state = 0; } int& get() noexcept { return value; } }; int& run(int input) noexcept { Cell cell(input); return cell.get(); }";
    let project = Project::with_fixture("expired.cpp", "run", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "expired.cpp";
Cell::Cell(int32 input) {
 owns this->value;
 owns this->state;
 ensures this->value == input;
 ensures this->state == 1;
}
Cell::~Cell() {
 owns this->state;
 ensures this->state == 0;
}
int32& Cell::get() {
 views this->value;
 ensures &result == &this->value;
 ensures result == old(this->value);
}
int32& run(int32 input) { ensures result == input; }
"#;
    let path = project.directory.join("expired.click");
    fs::write(&path, source).unwrap();
    let alias_only = source.replace(
        "int32& run(int32 input) { ensures result == input; }",
        "int32& run(int32 input) { ensures 1 == 1; }",
    );
    fs::write(&path, &alias_only).unwrap();
    verify_program_prepared_project(&read_click_project(&path, &alias_only).unwrap(), &import)
        .unwrap();
    fs::write(&path, source).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, source).unwrap(), &import)
            .unwrap_err();
    assert!(error.message().contains("run"), "{}", error.message());
    assert!(
        error.message().contains("resource") || error.message().contains("live"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn cpp_field_reference_results_preserve_addresses_and_backing_authority_offline() {
    let cpp = "struct Cell { int value; int& get() noexcept { return value; } }; int write(Cell& cell, int input) noexcept { int& element = cell.get(); element = input; return element; }";
    let project = Project::with_fixture("field.cpp", "write", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "field.cpp";
int32& Cell::get() {
 views this->value;
 ensures &result == &this->value;
 ensures result == old(this->value);
}
int32 write(struct Cell& cell, int32 input) {
 owns cell.value;
 ensures result == input;
 ensures cell.value == input;
}
"#;
    check_selected_claim_certificate(&project, &import, source);
    for bad in [
        source.replace(" owns cell.value;", " views cell.value;"),
        source.replace(
            " ensures &result == &this->value;",
            " ensures &result == &this->value + 1;",
        ),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
                .is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn cpp_const_field_reference_results_retain_qualification_offline() {
    let cpp = "struct Cell { int value; const int& get() const noexcept { return value; } }; const int& run(const Cell& cell) noexcept { return cell.get(); }";
    let project = Project::with_fixture("field.cpp", "run", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "field.cpp";
const int32& Cell::get() const {
 views this->value;
 ensures &result == &this->value;
 ensures result == old(this->value);
}
const int32& run(const struct Cell& cell) {
 views cell.value;
 ensures &result == &cell.value;
 ensures result == old(cell.value);
}
"#;
    check_return_call_sidecar(&project, &import, source);
    let bad = source.replace("const int32& run", "int32& run");
    let path = project.directory.join("bad.click");
    fs::write(&path, &bad).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn cpp_same_type_explicit_pointer_cast_preserves_identity_offline() {
    let project = Project::with_fixture(
        "pointer.cpp",
        "run",
        "int* run(int* input) noexcept { return static_cast<int*>(input); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "pointer.cpp";
int32* run(int32* input) { ensures result == input; }
"#;
    check_selected_claim_certificate(&project, &import, source);
}

// The child constructor is a modular call into the parent's field storage.
// Its generic proof cannot assume that the child's allocation ends there.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn embedded_member_constructor_preserves_parent_fields_and_backing_offline() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture(
        "embedded.cpp",
        "probe",
        r#"
struct Extent {
    unsigned long size;
    explicit Extent(unsigned long input) noexcept : size(input) {}
};
struct View {
    int* data;
    Extent extent;
    explicit View(int* backing, unsigned long count) noexcept : data(backing), extent(count) {}
};
unsigned long probe(int* backing, unsigned long count) noexcept {
    View view(backing, count);
    return view.extent.size;
}


"#,
    );
    refresh_import(&project.config()).expect("export resolved embedded constructor");
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let parent = import
        .export()
        .reachable_functions
        .iter()
        .find(|function| function.name == "View_constructor")
        .unwrap();
    assert!(matches!(
        parent.body[1],
        CppStatement::MemberConstruct { .. }
    ));
    let proof = r#"verifying "embedded.cpp";
Extent::Extent(uint64 input) {
 owns this->size;
 ensures this->size == input;
}
View::View(int32* backing, uint64 count) {
 owns this->data;
 owns this->extent.size;
 ensures this->data == backing;
 ensures this->extent.size == count;
}
uint64 probe(int32* backing, uint64 count) {
 views backing[0];
 ensures result == count;
 ensures backing[0] == old(backing[0]);
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    for label in [
        "Extent::Extent.contract",
        "View::View.contract",
        "probe.contract",
    ] {
        let expanded =
            expand_project_claim_source_by_label(&parsed, &ProgramInputs::program(&import), label)
                .unwrap();
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
    }
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let original_lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    let parent = original["reachable_functions"]
        .as_array()
        .unwrap()
        .iter()
        .position(|function| function["name"] == "View_constructor")
        .unwrap();
    for change in ["order", "reinitialize", "field", "arguments", "callee"] {
        let mut artifact = original.clone();
        let body = artifact["reachable_functions"][parent]["body"]
            .as_array_mut()
            .unwrap();
        match change {
            "order" => body.swap(0, 1),
            "reinitialize" => {
                let repeated = body[1].clone();
                body.insert(2, repeated);
            }
            "field" => body[1]["field"] = body[0]["field"].clone(),
            "arguments" => body[1]["arguments"].as_array_mut().unwrap().clear(),
            "callee" => {
                body[1]["callee"]["declaration_id"] =
                    original["reachable_functions"][parent]["declaration_id"].clone();
                body[1]["callee"]["name"] = original["reachable_functions"][parent]["name"].clone();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock = original_lock.clone();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "invalid member initialization: {change}"
        );
    }
}

// Construction at a nonzero offset must retain the child's own field address
// through both constructor summaries, without rebasing or copying the child.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn embedded_constructor_preserves_self_pointer_identity_offline() {
    let project = Project::with_fixture(
        "embedded.cpp",
        "probe",
        r#"
struct Node {
    int* self;
    int value;
    explicit Node(int input) noexcept : self(&value), value(input) {}
};
struct Parent {
    int prefix;
    Node child;
    explicit Parent(int input) noexcept : prefix(7), child(input) {}
};
int probe(int input) noexcept {
    Parent parent(input);
    return *parent.child.self;
}
"#,
    );
    refresh_import(&project.config()).expect("export embedded self-pointer constructor");
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "embedded.cpp";
Node::Node(int32 input) {
 owns this->self;
 owns this->value;
 ensures this->self == &this->value;
 ensures this->value == input;
}
Parent::Parent(int32 input) {
 owns this->prefix;
 owns this->child.self;
 owns this->child.value;
 ensures this->prefix == 7;
 ensures this->child.self == &this->child.value;
 ensures this->child.value == input;
}
int32 probe(int32 input) {
 ensures result == input;
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.ensures_0",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
}

// Locked, instantiated header constructors retain ordinary checked calls,
// including an observer initializer before nested member construction.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn locked_header_constructors_verify_observer_initializers_offline() {
    let mut project = Project::with_fixture(
        "header-construction.cpp",
        "probe",
        "#include \"descriptor.h\"\nunsigned long probe(int* backing, unsigned long count) { Descriptor descriptor(backing, count); return descriptor.extent.size; }\n",
    );
    let header = r#"
inline int* address(int* value) noexcept { return value; }
struct Extent {
    unsigned long size;
    Extent(unsigned long input) noexcept : size(input) {}
};
struct Descriptor {
    int* data;
    Extent extent;
    explicit(false) Descriptor(int* backing, unsigned long count) noexcept
        : data(address(backing)), extent(count) {}
};
"#;
    fs::write(project.directory.join("descriptor.h"), header).unwrap();
    project.dependencies.push("descriptor.h".into());
    project.write_exception_enabled_compilation_database();
    project.write_config_with_profile("probe", "header-construction.cpp", true);
    refresh_import(&project.config()).expect("export locked header constructor definitions");
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(
        import
            .export()
            .reachable_functions
            .iter()
            .all(|function| function.span.file == "descriptor.h")
    );
    let proof = r#"verifying "header-construction.cpp";
int32* address(int32* value) { ensures result == value; }
Extent::Extent(uint64 input) {
 owns this->size;
 ensures this->size == input;
}
Descriptor::Descriptor(int32* backing, uint64 count) {
 owns this->data;
 owns this->extent.size;
 ensures this->data == backing;
 ensures this->extent.size == count;
}
uint64 probe(int32* backing, uint64 count) {
 views backing[0];
 ensures result == count;
 ensures backing[0] == old(backing[0]);
}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "Descriptor::Descriptor.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
    fs::write(
        project.directory.join("descriptor.h"),
        format!("{header}\n// changed\n"),
    )
    .unwrap();
    assert!(
        load_import(&project.config()).is_err(),
        "changed constructor dependency must invalidate the lock"
    );
}

// Native result contracts use the same hidden storage through two factories;
// no parameter, slot clause or constructor inlining appears in the sidecar.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn construction_return_descriptor_factories_verify_offline() {
    check_construction_return_descriptor_factories(false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.6s ordinary, expanded and retained in the parallel gate"]
fn construction_return_descriptor_factories_expand_and_retain_offline() {
    check_construction_return_descriptor_factories(true);
}

fn check_construction_return_descriptor_factories(expand_and_retain: bool) {
    let project = Project::with_fixture(
        "construct-return.cpp",
        "probe",
        "int* identity(int* p) noexcept { return p; }\nint* address(int* p) noexcept { return identity(p); }\nstruct Extent { unsigned long size; explicit Extent(unsigned long n) noexcept : size(n) {} };\nstruct View { int* data; Extent extent; View(int* p, unsigned long n) noexcept : data(address(p)), extent(n) {} };\nView make(int* p, unsigned long n) noexcept { return {p, n}; }\nView forward(int* p, unsigned long n) noexcept { return make(p, n); }\nView relay(int* p, unsigned long n) noexcept { return forward(p, n); }\nunsigned long probe(int* p, unsigned long n) noexcept { View view = relay(p, n); return view.extent.size; }\n",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[0],
        CppStatement::Declare {
            initializer: CppInitializer::ConstructionCall { .. },
            ..
        }
    ));
    let lowered = lower_import(&import).unwrap();
    assert_eq!(
        lowered
            .reachable_kernel_functions()
            .iter()
            .find(|function| function.name() == "relay")
            .unwrap()
            .contract_interface()
            .aggregate_return_mode(),
        click::kernel::AggregateReturnMode::Construction
    );
    let proof = r#"verifying "construct-return.cpp";
int32* identity(int32* p) { ensures result == p; }
int32* address(int32* p) { ensures result == p; }
Extent::Extent(uint64 n) {
 owns this->size;
 ensures this->size == n;
}
View::View(int32* p, uint64 n) {
 owns this->data;
 owns this->extent.size;
 ensures this->data == p;
 ensures this->extent.size == n;
}
struct View make(int32* p, uint64 n) {
 ensures result.data == p;
 ensures result.extent.size == n;
}
struct View forward(int32* p, uint64 n) {
 ensures result.data == p;
 ensures result.extent.size == n;
}
struct View relay(int32* p, uint64 n) {
 ensures result.data == p;
 ensures result.extent.size == n;
}
uint64 probe(int32* p, uint64 n) {
 views p[0..1];
 ensures result == n;
 ensures p[0] == old(p[0]);
}
"#;
    check_arithmetic_sidecar_with_tools(&project, &import, proof, expand_and_retain);
    if !expand_and_retain {
        return;
    }
    let whole = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &whole,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&whole.with_entry_source(expanded), &import).unwrap();
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&whole, &import).unwrap();
    let position = project_tactic_source_position(
        &whole,
        &ProgramInputs::program(&import),
        "probe.ensures_0",
        0,
    )
    .unwrap();
    session
        .verify_at_project(proof, position.line, position.column)
        .unwrap();
}

// Trivial copying alone does not justify erasing construction storage identity
// or moving a constructor's aliasable memory observations to another object.
#[test]
fn construction_return_refuses_address_and_memory_sensitive_constructors_offline() {
    let valid = Project::with_fixture(
        "construct-return.cpp",
        "make",
        "struct View { int* data; View(int* p) noexcept : data(p) {} }; View make(int* p) noexcept { return View(p); }",
    );
    refresh_import(&valid.config()).expect("parenthesized prvalue construction remains admitted");
    use sha2::{Digest, Sha256};
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(valid.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value = serde_json::from_slice(&fs::read(valid.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        match mutation {
            0 => forged["functions"][0]["body"][0]["value_type"]["name"] = "Other".into(),
            1 => forged["functions"][0]["body"][0]["callee"]["declaration_id"] = "missing".into(),
            2 => forged["functions"][0]["body"][0]["arguments"] = serde_json::json!([]),
            3 => {
                forged["functions"][0]["body"][0]["cleanups"] = serde_json::json!([{
                    "kind": "destructor",
                "object": {"declaration_id":artifact["functions"][0]["parameters"][0]["declaration_id"],
                           "name":artifact["functions"][0]["parameters"][0]["name"],
                           "span":artifact["functions"][0]["parameters"][0]["span"]},
                "callee":artifact["functions"][0]["body"][0]["callee"],
                "span":artifact["functions"][0]["body"][0]["span"]
                }])
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(valid.artifact(), bytes).unwrap();
        fs::write(
            valid.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        assert!(
            load_import(&valid.config()).is_err(),
            "accepted returned-construction metadata mutation {mutation}"
        );
    }

    for source in [
        "struct Node { int* self; int value; Node(int n) noexcept : self(&value), value(n) {} }; Node make(int n) noexcept { return Node(n); }",
        "struct View { int value; View(int* p) noexcept : value(*p) {} }; View make(int* p) noexcept { return View(p); }",
        "int observe(int* p) noexcept { return *p; } struct View { int value; View(int* p) noexcept : value(observe(p)) {} }; View make(int* p) noexcept { return View(p); }",
        "struct View { int value; View(int* p) noexcept : value(7) { *p = 8; } }; View make(int* p) noexcept { return View(p); }",
    ] {
        let project = Project::with_fixture("construct-return.cpp", "make", source);
        let error = refresh_import(&project.config())
            .expect_err("storage-sensitive returned construction must remain outside the profile");
        assert!(
            error.contains("returned constructor"),
            "unexpected refusal: {error}"
        );
    }
}

// Assignment must read the old descriptor before updating it, and ending the
// trivial RHS temporary must preserve references into caller-held backing.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.5s in the parallel gate"]
fn construction_assignment_materializes_rhs_and_preserves_backing_offline() {
    check_construction_assignment(false);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.5s construction assignment expansion and retained verification"]
fn construction_assignment_expands_and_retains_offline() {
    check_construction_assignment(true);
}

fn check_construction_assignment(expand_and_retain: bool) {
    let project = Project::with_fixture(
        "construct-assignment.cpp",
        "probe",
        r#"int* identity(int* p) noexcept { return p; }
struct View {
 int* data;
 unsigned long size;
 View(int* p, unsigned long n) noexcept : data(identity(p)), size(n) {}
 View& operator=(const View&) noexcept = default;
};
View resize(const View& view, unsigned long n) noexcept { return View(view.data, n); }
unsigned long probe(View& view, unsigned long n) noexcept {
 int& back = *view.data;
 view = resize(view, n);
 back = 19;
 return view.size;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[1],
        click::languages::cpp::CppStatement::AssignConstructionCall { .. }
    ));
    let proof = r#"verifying "construct-assignment.cpp";
int32* identity(int32* p) { ensures result == p; }
View::View(int32* p, uint64 n) {
 owns this->data;
 owns this->size;
 ensures this->data == p;
 ensures this->size == n;
}
struct View resize(const struct View& view, uint64 n) {
 views view.data;
 ensures result.data == old(view.data);
 ensures result.size == n;
 ensures view.data == old(view.data);
}
uint64 probe(struct View& view, uint64 n) {
 owns view.data;
 owns view.size;
 owns view.data[0..1];
 ensures result == n;
 ensures view.data == old(view.data);
 ensures view.size == n;
 ensures view.data[0] == 19;
}
"#;
    check_arithmetic_sidecar_with_tools(&project, &import, proof, expand_and_retain);
    if !expand_and_retain {
        let missing = proof.replace(" owns view.data[0..1];", " views view.data[0..1];");
        let path = project.directory.join("bad.click");
        fs::write(&path, &missing).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &missing).unwrap(), &import)
                .is_err()
        );
        return;
    }
    let whole = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &whole,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&whole.with_entry_source(expanded), &import).unwrap();
    let (session, _) =
        ProgramVerificationSession::new_program_prepared_project(&whole, &import).unwrap();
    let position = project_tactic_source_position(
        &whole,
        &ProgramInputs::program(&import),
        "probe.ensures_0",
        0,
    )
    .unwrap();
    session
        .verify_at_project(proof, position.line, position.column)
        .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.3s in the parallel gate"]
// A saved reference remains readable under a backing view after the RHS
// descriptor temporary retires; pointer copying grants no new authority.
fn construction_assignment_saved_reference_read_offline() {
    let project = Project::with_fixture(
        "construct-assignment.cpp",
        "probe",
        r#"int* identity(int* p) noexcept { return p; }
struct View {
 int* data;
 unsigned long size;
 View(int* p, unsigned long n) noexcept : data(identity(p)), size(n) {}
 View& operator=(const View&) noexcept = default;
};
View resize(const View& view, unsigned long n) noexcept { return View(view.data, n); }
int& probe(View& view, unsigned long n) noexcept {
 int& back = *view.data;
 view = resize(view, n);
 return back;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[1],
        click::languages::cpp::CppStatement::AssignConstructionCall { .. }
    ));
    let proof = r#"verifying "construct-assignment.cpp";
int32* identity(int32* p) { ensures result == p; }
View::View(int32* p, uint64 n) {
 owns this->data;
 owns this->size;
 ensures this->data == p;
 ensures this->size == n;
}
struct View resize(const struct View& view, uint64 n) {
 views view.data;
 ensures result.data == old(view.data);
 ensures result.size == n;
 ensures view.data == old(view.data);
}
int32& probe(struct View& view, uint64 n) {
 owns view.data;
 owns view.size;
 views view.data[0..1];
 ensures &result == old(view.data);
 ensures result == old(view.data[0]);
 ensures view.data == old(view.data);
 ensures view.size == n;

}
"#;
    check_first_claim_certificate(&project, &import, proof);
    let missing = proof.replace(" views view.data[0..1];", "");
    let path = project.directory.join("missing.click");
    fs::write(&path, &missing).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &missing).unwrap(), &import)
            .is_err()
    );
}

// A symbolic last-element reference survives descriptor assignment and both
// temporary and local retirement; the original backing view is still required.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.9s symbolic saved-reference assignment and missing-view refusal"]
fn construction_assignment_saved_reference_offset_read_offline() {
    let project = Project::with_fixture(
        "construct-assignment.cpp",
        "probe",
        r#"int* identity(int* p) noexcept { return p; }
struct View {
 int* data;
 int size;
 View(int* p, int n) noexcept : data(identity(p)), size(n) {}
 View& operator=(const View&) noexcept = default;
};
View resize(const View& view, int n) noexcept { return View(view.data, n); }
int& last(const View& view) noexcept { return *(view.data + (view.size - 1)); }
int& probe(View& view, int n) noexcept {
 int size = view.size;
 int& back = last(view);
 view = resize(view, size - 1);
 return back;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().functions[0].body[2],
        click::languages::cpp::CppStatement::AssignConstructionCall { .. }
    ));
    let proof = r#"verifying "construct-assignment.cpp";
int32* identity(int32* p) { ensures result == p; }
View::View(int32* p, int32 n) {
 owns this->data;
 owns this->size;
 ensures this->data == p;
 ensures this->size == n;
}
struct View resize(const struct View& view, int32 n) {
 views view.data;
 ensures result.data == old(view.data);
 ensures result.size == n;
 ensures view.data == old(view.data);
}
int32& last(const struct View& view) {
 views view.data;
 views view.size;
 views view.data[0..view.size];
 requires 1 <= view.size;
 requires view.size <= 1073741823;
 ensures &result == old(view.data) + (old(view.size) - 1);
 ensures result == old(view.data[view.size - 1]);
} by { have 0 <= view.size - 1 by { close() using { 1 <= view.size; view.size <= 1073741823; } } have view.size - 1 < view.size by { close() using { 1 <= view.size; view.size <= 1073741823; } } step_until(function.exit); close(); }
int32& probe(struct View& view, int32 n) {
 owns view.data;
 owns view.size;
 views view.data[0..view.size];
 requires 1 <= view.size;
 requires view.size <= 1073741823;
 ensures &result == old(view.data) + (old(view.size) - 1);
 ensures result == old(view.data[view.size - 1]);
 ensures view.data == old(view.data);
 ensures view.size == old(view.size) - 1;

} by { have 0 <= view.size - 1 by { close() using { 1 <= view.size; view.size <= 1073741823; } } have view.size - 1 < view.size by { close() using { 1 <= view.size; view.size <= 1073741823; } } step_until(function.exit); close(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let missing = proof.replace(
        " views view.data[0..view.size];
 requires 1 <= view.size;
 requires view.size <= 1073741823;",
        "",
    );
    let path = project.directory.join("missing.click");
    fs::write(&path, &missing).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &missing).unwrap(), &import)
            .is_err()
    );
}

// Returned constructor arguments use the existing observer effect restriction,
// rather than selecting an arbitrary order for mutating argument expressions.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn returned_constructor_composed_observers_verify_and_reject_writes_offline() {
    let project = Project::with_fixture(
        "observe-result.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; struct Box { unsigned long value; explicit Box(unsigned long input) noexcept : value(input) {} }; Box probe(const Count& count) noexcept { return Box(count.size() + 1UL); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"import click::integer;
verifying "observe-result.cpp";
uint64 Count::size() const { views this->value; ensures result == this->value; }
Box::Box(uint64 input) { owns this->value; ensures this->value == input; }
struct Box probe(const struct Count& count) { views count.value; ensures result.value == integer::uint64_wrapping_add(count.value, 1u64); ensures count.value == old(count.value); }
"#;
    check_selected_claim_certificate(&project, &import, proof);
    let owning = proof
        .replace("views this->value", "owns this->value")
        .replace("views count.value", "owns count.value");
    fs::write(project.directory.join("bad.click"), &owning).unwrap();
    let error = verify_program_prepared_project(
        &read_click_project(&project.directory.join("bad.click"), &owning).unwrap(),
        &import,
    )
    .unwrap_err();
    assert!(
        error.message().contains("requires a read-only contract"),
        "{}",
        error.message()
    );
    let missing = proof.replace("views count.value;", "");
    fs::write(project.directory.join("missing.click"), &missing).unwrap();
    assert!(
        verify_program_prepared_project(
            &read_click_project(&project.directory.join("missing.click"), &missing).unwrap(),
            &import
        )
        .is_err()
    );
}

#[test]
fn returned_constructor_observers_refuse_mixed_nested_calls_offline() {
    let project = Project::with_fixture(
        "mixed-result.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; unsigned long echo(unsigned long n) noexcept { return n; } struct Box { unsigned long a; unsigned long b; explicit Box(unsigned long x, unsigned long y) noexcept : a(x), b(y) {} }; Box probe(const Count& count) noexcept { return Box(count.size() + 1UL, echo(2UL)); }",
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("value-only arguments"), "{error}");
}

// A locked header constant keeps its native high bits and its checked
// initializer; the frontend's evaluated value alone is insufficient evidence.
#[test]
fn locked_unsigned_header_constants_verify_and_reject_forged_values_offline() {
    let mut project = Project::with_fixture(
        "sentinel.cpp",
        "probe",
        "#include \"limits.h\"\nunsigned long probe() noexcept { if (limits::wide == 4294967299UL) return limits::end; return 0UL; }",
    );
    fs::write(project.directory.join("limits.h"), "namespace limits { inline constexpr unsigned long wide = 4294967299UL; inline constexpr unsigned long end = static_cast<unsigned long>(-1); }\n").unwrap();
    project.dependencies.push("limits.h".into());
    project.write_config_with_profile("probe", "sentinel.cpp", false);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof =
        "verifying \"sentinel.cpp\"; uint64 probe() { ensures result == 18446744073709551615u64; }";
    check_first_claim_certificate(&project, &import, proof);
    assert!(
        import
            .export()
            .constants
            .iter()
            .all(|constant| constant.span.file == "limits.h")
    );
    use sha2::{Digest, Sha256};
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        let constants = forged["constants"].as_array_mut().unwrap();
        let sentinel = constants
            .iter_mut()
            .find(|constant| constant["name"] == "end")
            .unwrap();
        match mutation {
            0 => sentinel["evaluated_value"] = "4294967295".into(),
            1 => sentinel["span"]["file"] = "unlocked.h".into(),
            2 => sentinel["initializer"]["value"]["right"]["value"] = "2".into(),
            3 => sentinel["initializer"]["value_type"]["signed"] = true.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        lock_source_mut(&mut forged_lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut forged_lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "mutation {mutation}"
        );
    }
}

// An observer RHS is evaluated once before assigning a scalar parameter or
// referent, and still cannot obtain a mutating contract or invent read authority.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn scalar_assignment_observers_verify_and_reject_writes_offline() {
    let project = Project::with_fixture(
        "assign-observer.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; unsigned long probe(const Count& count, unsigned long n) noexcept { n = count.size() + 1UL; return n; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "import click::integer;\nverifying \"assign-observer.cpp\"; uint64 Count::size() const { views this->value; ensures result == this->value; } uint64 probe(const struct Count& count, uint64 n) { views count.value; ensures result == integer::uint64_wrapping_add(count.value, 1u64); ensures count.value == old(count.value); }";
    check_selected_claim_certificate(&project, &import, proof);
    for bad in [
        proof
            .replace("views this->value", "owns this->value")
            .replace("views count.value", "owns count.value"),
        proof.replace("views count.value;", ""),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
                .is_err()
        );
    }
}

// Native object pointers retain their element type, stride and authority.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn cpp_native_word_and_byte_pointer_stores_verify_offline() {
    for (source_type, contract_type, literal) in [
        ("unsigned int", "uint32", "4294967295u32"),
        ("unsigned char", "uint8", "255u8"),
    ] {
        for access in ["*(p + 1)", "p[1]", "1[p]"] {
            let source = format!(
                "{source_type} probe({source_type}* p, {source_type} value) noexcept {{ {access} = value; return {access}; }}"
            );
            let project = Project::with_fixture("pointer.cpp", "probe", &source);
            refresh_import(&project.config()).unwrap();
            fs::remove_file(&project.exporter).unwrap();
            let import = load_import(&project.config()).unwrap();
            let sidecar = format!(
                "verifying \"pointer.cpp\"; {contract_type} probe({contract_type}* p, {contract_type} value) {{ owns p[0..2]; requires value == {literal}; ensures p[1] == value; ensures p[0] == old(p[0]); ensures result == value; }}"
            );
            check_selected_claim_certificate(&project, &import, &sidecar);
            let bad = sidecar.replace("owns p[0..2];", "views p[0..2];");
            let path = project.directory.join("bad.click");
            fs::write(&path, &bad).unwrap();
            let parsed = read_click_project(&path, &bad).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn cpp_native_scalar_addresses_initialize_automatic_storage_offline() {
    for (source_type, contract_type) in [("unsigned int", "uint32"), ("unsigned char", "uint8")] {
        let source = format!(
            "{source_type} probe({source_type} value) noexcept {{ {source_type} obj; *(&obj) = value; return obj; }}"
        );
        let project = Project::with_fixture("address.cpp", "probe", &source);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = format!(
            "verifying \"address.cpp\"; {contract_type} probe({contract_type} value) {{ ensures result == value; }}"
        );
        check_selected_claim_certificate(&project, &import, &sidecar);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn cpp_native_byte_field_address_uses_one_byte_storage_offline() {
    let project = Project::with_fixture(
        "field.cpp",
        "probe",
        "struct Pair { unsigned char a; unsigned char b; }; unsigned char probe(Pair& pair, unsigned char value) noexcept { *(&pair.b) = value; return pair.b; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"field.cpp\"; uint8 probe(struct Pair& pair, uint8 value) { owns pair.b; ensures pair.b == value; ensures result == value; }",
    );
}

#[test]
fn cpp_native_pointer_profile_refuses_generic_enums_and_other_character_types() {
    for ty in [
        "char",
        "signed char",
        "char8_t",
        "char16_t",
        "char32_t",
        "wchar_t",
        "unsigned long long",
        "Byte",
    ] {
        let source = format!(
            "enum class Byte : unsigned char {{}}; {ty} probe({ty}* p) noexcept {{ return *p; }}"
        );
        let project = Project::with_fixture("pointer.cpp", "probe", &source);
        assert!(refresh_import(&project.config()).is_err(), "{ty}");
    }
}

// Rehashed artifacts must not change a pointer's element type at loads,
// stores, or a resolved call boundary.
#[test]
fn cpp_native_pointer_artifacts_reject_pointee_substitution_offline() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture(
        "pointer.cpp",
        "probe",
        "unsigned char echo(unsigned char* p, unsigned char value) noexcept { *p = value; return *p; } unsigned char probe(unsigned char* p, unsigned char value) noexcept { return echo(p, value); }",
    );
    refresh_import(&project.config()).unwrap();
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let original_lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for change in ["load", "store", "call"] {
        let mut artifact = original.clone();
        match change {
            "load" => {
                artifact["reachable_functions"][0]["body"][1]["value"]["pointer"]["value_type"]["pointee"]
                    ["bits"] = 32.into()
            }
            "store" => {
                artifact["reachable_functions"][0]["body"][0]["pointer"]["value_type"]["pointee"]
                    ["bits"] = 32.into()
            }
            "call" => {
                artifact["functions"][0]["parameters"][0]["value_type"]["pointee"]["bits"] =
                    32.into();
                artifact["functions"][0]["body"][0]["arguments"][0]["value"]["value_type"]["pointee"]
                    ["bits"] = 32.into();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock = original_lock.clone();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        assert!(load_import(&project.config()).is_err(), "{change}");
    }
}

// Scalar allocation ownership can enter and return from a modular write.
// Ownership alone must not let a call read an uninitialized local.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn cpp_native_scalar_modular_write_uses_allocation_ownership_offline() {
    let project = Project::with_fixture(
        "initialize.cpp",
        "probe",
        "void fill(unsigned int* p, unsigned int value) noexcept { *p = value; } unsigned int probe(unsigned int value) noexcept { unsigned int obj = 0; fill(&obj, value); return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"initialize.cpp\"; void fill(uint32* p, uint32 value) { owns p[0..1]; ensures p[0] == value; } uint32 probe(uint32 value) { ensures result == value; }";
    check_return_call_sidecar(&project, &import, proof);
    let stale_claim = proof.replace("result == value", "result == 0");
    let path = project.directory.join("stale.click");
    fs::write(&path, &stale_claim).unwrap();
    let parsed = read_click_project(&path, &stale_claim).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .expect_err("a modular write must invalidate the old scalar value");
}

#[test]
fn cpp_native_scalar_modular_ownership_does_not_imply_initialization_offline() {
    let project = Project::with_fixture(
        "initialize.cpp",
        "probe",
        "void fill(unsigned int* p, unsigned int value) noexcept { *p = value; } unsigned int probe(unsigned int value) noexcept { unsigned int obj; fill(&obj, value); return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"initialize.cpp\"; void fill(uint32* p, uint32 value) { owns p[0..1]; ensures p[0] == value; } uint32 probe(uint32 value) { ensures result == value; }";
    let path = project.directory.join("uninitialized.click");
    fs::write(&path, proof).unwrap();
    let parsed = read_click_project(&path, proof).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("ordinary ownership and a value postcondition do not certify initialization");
    assert!(error.message().contains("uninitialized"), "{error:?}");
}

fn axiomatic_project(header_prefix: &str) -> Project {
    let mut project = Project::with_fixture(
        "driver.cpp",
        "forward",
        "#include \"mini_std.h\"\nint* forward(int* p) noexcept { return ministd::identity(p); }\n",
    );
    fs::write(
        project.directory.join("mini_std.h"),
        format!(
            "{header_prefix}namespace ministd {{\ninline int* identity(int* p) noexcept {{ return p; }}\n}}\n"
        ),
    )
    .unwrap();
    if header_prefix.is_empty() {
        project.dependencies.push("mini_std.h".into());
        project.write_config("forward");
    }
    project
}

// A system-header function is exported as an interface with no body, and
// its call is checked against the contract Click is given for it; without
// one, the caller does not verify.
#[test]
fn axiomatic_system_header_calls_export_interfaces_only() {
    let project = axiomatic_project("#pragma clang system_header\n");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [axiom] = import.export().reachable_functions.as_slice() else {
        panic!("one reachable axiom")
    };
    let identity = axiom.axiom.as_ref().expect("an axiom");
    assert_eq!(identity.qualified_name, "ministd::identity");
    assert!(axiom.body.is_empty());
    assert!(import.export().dependencies.is_empty());
    let sidecar = project.directory.join("forward.click");
    assert_eq!(axiom.name, "ministd_identity");
    // The `extern` head is the C++ declaration, qualified name and all.
    let assumed = "verifying \"driver.cpp\";\nextern int* ministd::identity(int* p) { ensures result == p; }\nint* forward(int* p) { ensures result == p; }\n";
    fs::write(&sidecar, assumed).unwrap();
    let parsed = read_click_project(&sidecar, assumed).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    let unassumed =
        "verifying \"driver.cpp\";\nint32* forward(int32* p) { ensures result == p; }\n";
    fs::write(&sidecar, unassumed).unwrap();
    let parsed = read_click_project(&sidecar, unassumed).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        click::surface::display_source_names(error.message()).contains("ministd::identity"),
        "{}",
        error.message()
    );

    // The same function in a project header is program code: its body is
    // exported and verified.
    let project = axiomatic_project("");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [verified] = import.export().reachable_functions.as_slice() else {
        panic!("one reachable definition")
    };
    assert!(verified.axiom.is_none());
    assert!(!verified.body.is_empty());

    let project = axiomatic_project("#pragma clang system_header\n");
    let header = project.directory.join("mini_std.h");
    let potentially_throwing = fs::read_to_string(&header)
        .unwrap()
        .replace(" noexcept", "");
    fs::write(header, potentially_throwing).unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("ministd::identity")
            && error.contains("must be noexcept or have a nonthrowing catalog contract"),
        "{error}"
    );
}

#[test]
fn layout_free_cpp_references_forward_to_contracts() {
    let project = Project::with_fixture(
        "driver.cpp",
        "read",
        "struct Buffer;\nunsigned long length(const Buffer& buffer) noexcept;\nunsigned long read(const Buffer& buffer) noexcept { return length(buffer); }\n",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [record] = import.export().records.as_slice() else {
        panic!("one nominal record declaration")
    };
    assert_eq!(record.path, ["Buffer"]);
    assert_eq!((record.size_bytes, record.alignment_bytes), (0, 0));
    assert!(record.fields.is_empty());
    let path = project.directory.join("read.click");
    fs::write(project.directory.join("buffer.interface.click"),
        "abstract resource buffer_state(buffer: const void*) { field count: uint64; }\nunsigned long length(const Buffer& buffer) { owns state: buffer_state(&buffer); ensures state.count == old(state.count); ensures result == state.count; }\n"
    ).unwrap();
    let source = "import \"buffer.interface.click\";\nverifying \"driver.cpp\";\nunsigned long read(const Buffer& buffer) { owns state: buffer_state(&buffer); ensures state.count == old(state.count); ensures result == state.count; }\n";
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}", error.report()));
    let missing_state = "import \"buffer.interface.click\";\nverifying \"driver.cpp\";\nunsigned long read(const Buffer& buffer) { ensures result == result; }\n";
    let parsed = read_click_project(&path, missing_state).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.report().contains("unbound instance binder `state`"),
        "{}",
        error.report()
    );

    // Rehash a forged artifact so the nominal record validator sees it.
    use sha2::{Digest, Sha256};
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    artifact["records"][0]["fields"] = serde_json::json!([{
        "declaration_id": "forged_field",
        "name": "field",
        "value_type": { "kind": "integer", "bits": 32, "signed": true, "is_const": false, "source_aliases": [] },
        "offset_bytes": 0,
        "size_bytes": 4,
        "span": artifact["records"][0]["span"],
    }]);
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    let bytes = serde_json::to_vec(&artifact).unwrap();
    lock_source_mut(&mut lock)["artifact"]["sha256"] =
        format!("{:x}", Sha256::digest(&bytes)).into();
    lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
    fs::write(project.artifact(), bytes).unwrap();
    fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(
        error.contains("supplies storage or lifetime metadata"),
        "{error}"
    );
}

#[test]
fn layout_free_cpp_pointers_forward_to_contracts() {
    let project = Project::with_fixture(
        "driver.cpp",
        "read",
        "struct Buffer;\nunsigned long length(Buffer* buffer) noexcept;\nunsigned long read(Buffer* buffer) noexcept { return length(buffer); }\n",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [record] = import.export().records.as_slice() else {
        panic!("one nominal record declaration")
    };
    assert_eq!(record.path, ["Buffer"]);
    assert_eq!((record.size_bytes, record.alignment_bytes), (0, 0));
    assert!(record.fields.is_empty());

    fs::write(
        project.directory.join("buffer.interface.click"),
        r#"abstract resource buffer_state(buffer: Buffer*) { field count: uint64; }
unsigned long length(Buffer* buffer) {
    owns state: buffer_state(buffer);
    ensures state.count == old(state.count);
    ensures result == state.count;
}
"#,
    )
    .unwrap();
    let path = project.directory.join("read.click");
    let source = r#"import "buffer.interface.click";
verifying "driver.cpp";
unsigned long read(Buffer* buffer) {
    owns state: buffer_state(buffer);
    ensures state.count == old(state.count);
    ensures result == state.count;
}
"#;
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}", error.report()));

    let missing_state = r#"import "buffer.interface.click";
verifying "driver.cpp";
unsigned long read(Buffer* buffer) { ensures result == result; }
"#;
    let parsed = read_click_project(&path, missing_state).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.report().contains("unbound instance binder `state`"),
        "{}",
        error.report()
    );
}

const BYTE_VECTOR_FIXTURE_HEADER: &str = r#"#pragma clang system_header
namespace std {
template<class T> struct allocator;
template<class T, class A = allocator<T>> class vector {
    A* allocator;
    T* storage;
public:
    ~vector() noexcept;
    unsigned long size() const noexcept;
    bool empty() const noexcept;
    const T* data() const noexcept;
};
}
"#;

#[test]
fn cpp_memcpy_copies_initialized_bytes_through_implicit_void_conversions() {
    let project = Project::with_fixture(
        "driver.cpp",
        "probe",
        r#"#include "copy.h"
unsigned char probe(unsigned char* destination, const unsigned char* source) noexcept {
    memcpy(destination, source, 1);
    return destination[0];
}
"#,
    );
    fs::write(
        project.directory.join("copy.h"),
        "#pragma clang system_header\nextern \"C\" void* memcpy(void*, const void*, unsigned long) noexcept;\n",
    )
    .unwrap();
    project.write_config("probe");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    // Read the fresh capture directly, before the importer normalizes older spellings.
    let captured: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    assert!(
        captured["reachable_functions"][0]["parameters"]
            .as_array()
            .unwrap()
            .iter()
            .all(|parameter| parameter["name"] == "")
    );
    let lowered = lower_import(&import).unwrap();
    let reachable = &lowered.reachable_kernel_functions()[0];
    let parameters = reachable.parameters();
    let interface = lowered
        .contract_functions()
        .iter()
        .find(|function| function.name() == reachable.name())
        .unwrap();
    assert_eq!(parameters.len(), 3);
    assert!(
        interface
            .parameters()
            .iter()
            .map(|parameter| parameter.binding_name())
            .eq(parameters.iter().map(|parameter| parameter.binding_name()))
    );
    for (index, parameter) in parameters.iter().enumerate() {
        let click::kernel::BindingName::Local(identity) = parameter.binding_name() else {
            panic!("unnamed parameter has a typed declaration identity")
        };
        assert_eq!(identity.ordinal() as usize, index);
        assert!(identity.is_parameter());
        assert!(identity.spelling().is_none());
    }
    let source = r#"verifying "driver.cpp";
uint8 probe(uint8* destination, const uint8* source) {
    owns uninitialized(destination[0..1]);
    views source[0..1];
    ensures result == old(source[0]);
} by {
    step();
    have destination[0] == old(source[0]) by {
        instantiate(forall (k: uint64) {
            true and k < 1u64 implies destination[0u64 + k] == old(source[0u64 + k])
        }, 0u64);
        close();
    }
    step_until(function.exit);
}
"#;
    let path = project.directory.join("copy.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    let (summary, verification) =
        click::surface::verify_project_with_summary(&parsed, &ProgramInputs::program(&import))
            .unwrap_or_else(|error| panic!("{}", error.report()));
    verification.unwrap_or_else(|error| panic!("{}", error.report()));
    assert!(summary.assumptions["probe"].iter().any(|assumption| {
        assumption.family == click::surface::ModelFamily::CppStd && assumption.name == "memcpy"
    }));
    let missing_write = source.replace(
        "owns uninitialized(destination[0..1]);",
        "views destination[0..1];",
    );
    let parsed = read_click_project(&path, &missing_write).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.report().contains("memcpy"), "{}", error.report());
}

#[test]
fn byte_vector_size_uses_a_layout_free_catalog_contract() {
    let project = Project::with_fixture(
        "driver.cpp",
        "read",
        "#include \"vector_fixture.h\"\nunsigned long read(const std::vector<unsigned char>& bytes) noexcept { return bytes.size(); }\n",
    );
    fs::write(
        project.directory.join("vector_fixture.h"),
        BYTE_VECTOR_FIXTURE_HEADER,
    )
    .unwrap();
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [record] = import.export().records.as_slice() else {
        panic!("one nominal record declaration")
    };
    assert_eq!(record.path, ["std", "vector<unsigned char>"]);
    assert_eq!((record.size_bytes, record.alignment_bytes), (0, 0));
    assert!(record.fields.is_empty());
    assert!(import.export().dependencies.is_empty());
    assert!(import.export().reachable_functions[0].body.is_empty());
    let path = project.directory.join("read.click");
    let source = "import click::cpp::vector_state::{vector_state};\nverifying \"driver.cpp\";\nunsigned long read(const std::vector<unsigned char>& bytes) { owns state: vector_state(&bytes); ensures state.length == old(state.length); ensures result == state.length; }\n";
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    let (summary, verification) =
        click::surface::verify_project_with_summary(&parsed, &ProgramInputs::program(&import))
            .unwrap_or_else(|error| panic!("{}", error.report()));
    verification.unwrap_or_else(|error| panic!("{}", error.report()));
    assert!(
        click::surface::display_source_names(&format!("{:?}", summary.assumptions))
            .contains("std::vector<unsigned char>::size"),
        "{:?}",
        summary.assumptions
    );
    let missing_state = "verifying \"driver.cpp\";\nunsigned long read(const std::vector<unsigned char>& bytes) { ensures result == result; }\n";
    let parsed = read_click_project(&path, missing_state).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.report().contains("unbound instance binder `state`"),
        "{}",
        error.report()
    );
}

#[test]
fn byte_vector_empty_and_data_require_the_catalog_state() {
    let project = Project::with_fixture(
        "driver.cpp",
        "read",
        "#include \"vector_fixture.h\"\nbool read(const std::vector<unsigned char>& bytes) noexcept { const unsigned char* ptr = bytes.data(); return bytes.empty(); }\n",
    );
    fs::write(
        project.directory.join("vector_fixture.h"),
        BYTE_VECTOR_FIXTURE_HEADER,
    )
    .unwrap();
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"import click::cpp::vector_state::{vector_state};
verifying "driver.cpp";
bool read(const std::vector<unsigned char>& bytes) {
    owns state: vector_state(&bytes);
    ensures state.length == old(state.length);
    ensures state.data == old(state.data);
    ensures state.length == 0u64 implies result;
    ensures state.length != 0u64 implies not result;
}
"#;
    let path = project.directory.join("read.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    let (summary, verification) =
        click::surface::verify_project_with_summary(&parsed, &ProgramInputs::program(&import))
            .unwrap_or_else(|error| panic!("{}", error.report()));
    verification.unwrap_or_else(|error| panic!("{}", error.report()));
    let assumptions = &summary.assumptions["read"];
    for method in ["empty", "data"] {
        let name = format!("std::vector<unsigned char>::{method}");
        assert!(
            assumptions.iter().any(|assumption| {
                assumption.family == click::surface::ModelFamily::CppStd
                    && click::surface::display_source_names(&assumption.name) == name
            }),
            "{assumptions:?}"
        );
    }

    let missing_state = r#"verifying "driver.cpp";
bool read(const std::vector<unsigned char>& bytes) { ensures result or not result; }
"#;
    let parsed = read_click_project(&path, missing_state).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.report().contains("unbound instance binder `state`"),
        "{}",
        error.report()
    );
}

// The interface head of a system-header member function is its C++
// declaration: the qualified member name, `const`, and an implicit `this`.
// Writing `this` out is refused, as it is in a verified function's head.
#[test]
fn axiomatic_member_function_heads_in_interfaces_are_cpp_declarations() {
    let mut project = Project::with_fixture(
        "driver.cpp",
        "read",
        "#include \"mini_std.h\"\nint read(const ministd::Box& box) noexcept { return box.get(); }\n",
    );
    fs::write(
        project.directory.join("mini_std.h"),
        "#pragma clang system_header\nnamespace ministd {\nstruct Box { int value; int get() const noexcept { return value; } };\n}\n",
    )
    .unwrap();
    project.dependencies.push("mini_std.h".into());
    project.write_config("read");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let [axiom] = import.export().reachable_functions.as_slice() else {
        panic!("one reachable axiom")
    };
    assert_eq!(axiom.name, "Box_get");
    let sidecar = project.directory.join("read.click");
    let interface = project.directory.join("box.interface.click");
    let native =
        "int ministd::Box::get() const { views this->value; ensures result == this->value; }\n";
    let source = "import \"box.interface.click\";\nverifying \"driver.cpp\";\nint read(const Box& box) { views box.value; ensures result == box.value; }\n";
    fs::write(&interface, native).unwrap();
    fs::write(&sidecar, source).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    let explicit = native.replace(
        "int ministd::Box::get() const",
        "int Box_get(const Box* this)",
    );
    fs::write(&interface, explicit).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.message().contains("`this` is implicit"),
        "{}",
        error.message()
    );
}

#[test]
// An unsigned-char-backed user enum must not acquire standard byte authority,
// even when it uses the reserved spelling in a synthetic source declaration.
fn cpp_standard_byte_pointer_requires_the_pinned_declaration() {
    let project = Project::with_fixture(
        "byte.cpp",
        "probe",
        "namespace std { enum class byte : unsigned char {}; } std::byte probe(std::byte* p) noexcept { return *p; }",
    );
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("std::byte"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
// Native pointer locals use ordinary scalar allocation and assignment; keeping
// their pointee types avoids treating the local's storage as its referent.
fn cpp_initialized_native_pointer_locals_reassign_offline() {
    let project = Project::with_fixture(
        "pointer-local.cpp",
        "probe",
        "unsigned char* probe(unsigned char* p, unsigned char* q) noexcept { unsigned char* local = p; local = q; return local; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(
        &project,
        &import,
        "verifying \"pointer-local.cpp\"; uint8* probe(uint8* p, uint8* q) { ensures result == q; }",
    );
}

#[test]
fn cpp_byte_reinterpretation_profile_refuses_nonbyte_and_reverse_casts() {
    for source in [
        "enum class Other : unsigned char {}; Other* probe(unsigned int* p) noexcept { return reinterpret_cast<Other*>(p); }",
        "unsigned int* probe(unsigned char* p) noexcept { return reinterpret_cast<unsigned int*>(p); }",
        "unsigned char* probe(unsigned int* p) noexcept { return reinterpret_cast<unsigned char*>(p); }",
        "unsigned char* probe(unsigned char* p) noexcept { unsigned char* q; q = p; return q; }",
    ] {
        let project = Project::with_fixture("cast.cpp", "probe", source);
        assert!(refresh_import(&project.config()).is_err());
        assert!(!project.artifact().exists());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
// Preserve the former refusal's original C++ source: its native pointer local
// now borrows the reference without acquiring write authority.
fn cpp_native_pointer_local_from_reference_verifies_offline() {
    let project = Project::with_fixture(
        "bump_reference.cpp",
        "bump_reference",
        "int bump_reference(int& value) noexcept {\n    int* pointer = &value;\n    return *pointer;\n}\n",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"bump_reference.cpp\"; int32 bump_reference(int32& value) { views value; ensures result == value; ensures value == old(value); }",
    );
}

// A C++ function pointer is a callback, as in C: `apply` calls through `f`
// under the named contract it requires of `f`, and `caller` passes `&twice`,
// which the `executes` theorem shows meets that contract.
const FUNCTION_POINTER_SOURCE: &str = "int twice(int x) noexcept { return x + x; }\n\
int apply(int (*f)(int) noexcept, int x) noexcept { return f(x); }\n\
int caller(int x) noexcept { return apply(&twice, x); }\n";

const FUNCTION_POINTER_SIDECAR: &str = r#"verifying "callback.cpp";
contract int Doubling(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int twice(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
theorem twice_doubles() {
    ensures Doubling(&twice) by { unfold(Doubling(&twice)); close(); }
}
int apply(int (*f)(int), int x) {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int caller(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { apply(twice_doubles()); step_until(function.exit); close(); }
"#;

// A pointer call may be a returned call, a local's initializer, or a
// statement whose result is discarded.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn calls_through_a_cpp_function_pointer_meet_its_named_contract() {
    let returned = "return f(x);";
    for body in [returned, "int y = f(x); f(x); return y;"] {
        let source = FUNCTION_POINTER_SOURCE.replace(returned, body);
        let project = Project::with_fixture("callback.cpp", "caller", &source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = project.directory.join("callback.click");
        fs::write(&sidecar, FUNCTION_POINTER_SIDECAR).unwrap();
        let parsed = read_click_project(&sidecar, FUNCTION_POINTER_SIDECAR).unwrap();
        verify_program_prepared_project(&parsed, &import)
            .unwrap_or_else(|error| panic!("{body}: {}", error.message()));
        if body == returned {
            // The expanded proofs of the pointer call and of the caller
            // passing `&twice` reverify.
            for label in ["apply.ensures_0", "caller.contract"] {
                let expanded = expand_project_claim_source_by_label(
                    &parsed,
                    &ProgramInputs::program(&import),
                    label,
                )
                .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
                verify_program_prepared_project(&parsed.with_entry_source(expanded), &import)
                    .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
            }
        }
    }
}

// The call through `f` needs the contract `apply` requires of it, and the
// call passing `&twice` needs `twice` to meet that contract: through the
// refinement theorem, or, since `Doubling` reads no memory, formed
// automatically from `twice`'s own contract. A contract that does not imply
// `Doubling` is refused either way.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn a_cpp_function_pointer_call_needs_its_contract_and_its_refinement() {
    let project = Project::with_fixture("callback.cpp", "caller", FUNCTION_POINTER_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = project.directory.join("callback.click");
    let theorem = "theorem twice_doubles() {\n    ensures Doubling(&twice) by { unfold(Doubling(&twice)); close(); }\n}\n";
    let without_theorem = FUNCTION_POINTER_SIDECAR
        .replace(theorem, "")
        .replace("apply(twice_doubles()); ", "");
    let verify = |source: &str| {
        fs::write(&sidecar, source).unwrap();
        let parsed = read_click_project(&sidecar, source).unwrap();
        verify_program_prepared_project(&parsed, &import)
    };
    verify(FUNCTION_POINTER_SIDECAR).unwrap_or_else(|error| panic!("{}", error.message()));
    verify(&without_theorem).unwrap_or_else(|error| panic!("{}", error.message()));
    let weak_twice = "    ensures result >= 0;\n}";
    let weak_without_theorem = without_theorem.replace(
        "int twice(int x) {\n    requires 0 <= x and x <= 1000;\n    ensures result == x + x;\n}",
        &format!("int twice(int x) {{\n    requires 0 <= x and x <= 1000;\n{weak_twice}"),
    );
    assert_ne!(weak_without_theorem, without_theorem);
    let error = verify(&weak_without_theorem).expect_err("a weaker callback must not form");
    assert!(
        error
            .message()
            .contains("does not satisfy named contract `Doubling` automatically"),
        "{}",
        error.message()
    );
    for hostile in [
        FUNCTION_POINTER_SIDECAR.replace("    requires Doubling(f);\n", ""),
        FUNCTION_POINTER_SIDECAR.replacen(
            "    ensures result == x + x;\n}\nint twice",
            "    ensures result == x + x + 1;\n}\nint twice",
            1,
        ),
        FUNCTION_POINTER_SIDECAR.replace(
            "int twice(int x) {\n    requires 0 <= x and x <= 1000;\n    ensures result == x + x;\n}",
            &format!("int twice(int x) {{\n    requires 0 <= x and x <= 1000;\n{weak_twice}"),
        ),
    ] {
        assert_ne!(hostile, FUNCTION_POINTER_SIDECAR);
        let Err(error) = verify(&hostile) else {
            panic!("accepted:\n{hostile}");
        };
        if hostile.contains(weak_twice) {
            assert!(
                error
                    .message()
                    .contains("contract-refinement proof does not establish `Doubling(&twice)`"),
                "{}",
                error.message()
            );
        }
    }
}

const STORED_FUNCTION_POINTER_SOURCE: &str = "int twice(int x) noexcept { return x + x; }\n\
int stored(int (*f)(int) noexcept, int x) noexcept {\n\
    int (*g)(int) noexcept = f;\n\
    return g(x);\n\
}\n\
int relay(int (*f)(int) noexcept, int x) noexcept { return stored(f, x); }\n\
int caller(int x) noexcept {\n\
    int (*h)(int) noexcept = &twice;\n\
    return relay(h, x);\n\
}\n";

const STORED_FUNCTION_POINTER_SIDECAR: &str = r#"verifying "callback.cpp";
contract int Doubling(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int twice(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
theorem twice_doubles() {
    ensures Doubling(&twice) by { unfold(Doubling(&twice)); close(); }
}
int stored(int (*f)(int), int x) {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int relay(int (*f)(int), int x) {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int caller(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { apply(twice_doubles()); }
"#;

// A function-pointer local holds `&twice` or a parameter's pointer, a call
// goes through the local, and a parameter or local is passed on. The
// contract follows the pointer: each function that calls through it or
// passes it on requires it, and `caller` shows `twice` meets it.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn stored_and_forwarded_cpp_function_pointers_keep_their_contract() {
    let project = Project::with_fixture("callback.cpp", "caller", STORED_FUNCTION_POINTER_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = project.directory.join("callback.click");
    let verify = |source: &str| {
        fs::write(&sidecar, source).unwrap();
        let parsed = read_click_project(&sidecar, source).unwrap();
        verify_program_prepared_project(&parsed, &import).map(|_| parsed)
    };
    let parsed = verify(STORED_FUNCTION_POINTER_SIDECAR)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    for label in ["stored.ensures_0", "relay.ensures_0", "caller.ensures_0"] {
        let expanded =
            expand_project_claim_source_by_label(&parsed, &ProgramInputs::program(&import), label)
                .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import)
            .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
    }
    let requirement = |function: &str| {
        format!("int {function}(int (*f)(int), int x) {{\n    requires Doubling(f);\n")
    };
    for (function, expected) in [
        ("stored", "cannot verify call through function pointer `g`"),
        (
            "relay",
            "requires an explicit prerequisite proof (precondition clause 1 of `stored`)",
        ),
    ] {
        let hostile = STORED_FUNCTION_POINTER_SIDECAR.replace(
            &requirement(function),
            &format!("int {function}(int (*f)(int), int x) {{\n"),
        );
        assert_ne!(hostile, STORED_FUNCTION_POINTER_SIDECAR);
        let Err(error) = verify(&hostile) else {
            panic!("accepted:\n{hostile}");
        };
        assert!(error.message().contains(expected), "{}", error.message());
    }
    let weak_twice = STORED_FUNCTION_POINTER_SIDECAR.replacen(
        "    ensures result == x + x;\n}\ntheorem twice_doubles",
        "    ensures result >= 0;\n}\ntheorem twice_doubles",
        1,
    );
    assert_ne!(weak_twice, STORED_FUNCTION_POINTER_SIDECAR);
    let Err(error) = verify(&weak_twice) else {
        panic!("accepted a `twice` that does not meet `Doubling`");
    };
    assert!(
        error
            .message()
            .contains("contract-refinement proof does not establish `Doubling(&twice)`"),
        "{}",
        error.message()
    );
}

// The importer admits a call through a pointer to a noexcept function, in
// a variable, with value arguments; it refuses the rest by name.
#[test]
fn cpp_function_pointer_shapes_outside_the_profile_are_refused() {
    for (source, expected) in [
        (
            "int twice(int x) { return x + x; }\nint apply(int (*f)(int), int x) noexcept { return f(x); }\nint caller(int x) noexcept { return apply(&twice, x); }\n",
            "noexcept, non-variadic function",
        ),
        (
            "int twice(int x) noexcept { return x + x; }\nint apply(int (*f)(int) noexcept, int x) noexcept { int (*g)(int) noexcept = f; g = f; return g(x); }\nint caller(int x) noexcept { return apply(&twice, x); }\n",
            "C++ assignment target is not a mutable reference or local",
        ),
        (
            "int twice(int x) noexcept { return x + x; }\nint apply(int (*f)(int) noexcept, int x) noexcept { return f(twice(x)); }\nint caller(int x) noexcept { return apply(&twice, x); }\n",
            "takes no call as an argument",
        ),
        (
            "int twice(int x) noexcept { return x + x; }\nint apply(int (*f)(int) noexcept, int x) noexcept { return twice(f(x)); }\nint caller(int x) noexcept { return apply(&twice, x); }\n",
            "not admitted as a call argument",
        ),
    ] {
        let project = Project::with_fixture("callback.cpp", "caller", source);
        let error = refresh_import(&project.config())
            .and_then(|()| load_import(&project.config()).map(|_| ()))
            .unwrap_err();
        assert!(error.contains(expected), "{error}");
    }
}

// The importer checks a function pointer's uses in the artifact itself: an
// address has its function's type, a pointer call goes through a
// function-pointer variable, and an ordinary call names a function.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn forged_cpp_function_pointer_artifacts_are_refused() {
    use sha2::{Digest, Sha256};
    for (change, expected) in [
        ("address_type", "does not have its function's type"),
        ("address_function", "does not have its function's type"),
        (
            "pointer_variable",
            "requires a function-pointer parameter or local",
        ),
        ("direct_pointer", "missing reachable definition"),
    ] {
        let project = Project::with_fixture("callback.cpp", "caller", FUNCTION_POINTER_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let mut artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let apply_index = artifact["reachable_functions"]
            .as_array()
            .unwrap()
            .iter()
            .position(|function| function["name"] == "apply")
            .unwrap();
        let apply = artifact["reachable_functions"][apply_index].clone();
        let address = &mut artifact["functions"][0]["body"][0]["arguments"][0]["value"];
        assert_eq!(address["kind"], "function_address");
        match change {
            "address_type" => address["value_type"]["parameters"][0]["bits"] = 64.into(),
            "address_function" => {
                address["function"]["declaration_id"] = apply["declaration_id"].clone();
                address["function"]["name"] = "apply".into();
            }
            "pointer_variable" | "direct_pointer" => {
                let call = &mut artifact["reachable_functions"][apply_index]["body"][0]["callee"];
                assert_eq!(call["through_pointer"], true);
                if change == "pointer_variable" {
                    call["declaration_id"] = apply["parameters"][1]["declaration_id"].clone();
                    call["name"] = "x".into();
                } else {
                    call.as_object_mut().unwrap().remove("through_pointer");
                }
            }
            _ => unreachable!(),
        }
        let mut lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        let bytes = serde_json::to_vec(&artifact).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.contains(expected), "{change}: {error}");
    }
}

const LAMBDA_SOURCE: &str = "int apply(int (*f)(int) noexcept, int x) noexcept { return f(x); }\n\
int caller(int x) noexcept {\n\
    return apply([](int y) noexcept { return y + y; }, x);\n\
}\n\
int pair(int x) noexcept {\n\
    return apply([](int y) noexcept { return y + 1; }, x) + apply([](int y) noexcept { return y + y; }, x);\n\
}\n";

const LAMBDA_SIDECAR: &str = r#"verifying "callback.cpp";
contract int Doubling(int x) {
    requires 0 <= x and x <= 1000;
    ensures 0 <= result and result <= 2000;
    ensures result == x + x;
}
contract int Bounded(int x) {
    requires 0 <= x and x <= 1000;
    ensures 0 <= result and result <= 2000;
}
int apply(int (*f)(int), int x) {
    requires Doubling(f);
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
}
int caller::(lambda#0)(int y) {
    requires 0 <= y and y <= 1000;
    ensures 0 <= result and result <= 2000;
    ensures result == y + y;
}
theorem lambda_doubles() {
    ensures Doubling(&caller::(lambda#0)) by { unfold(Doubling(&caller::(lambda#0))); close(); }
}
int caller(int x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + x;
} by { apply(lambda_doubles()); }
"#;

// A lambda that captures nothing, passed for a function pointer, is its call
// operator's address. The sidecar names the call operator by its enclosing
// function and its index there, `caller::(lambda#0)`, verifies it like any
// function, and a caller passing it must show it meets the contract the
// callee requires of the pointer.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn cpp_lambdas_passed_for_a_function_pointer_meet_its_named_contract() {
    let project = Project::with_fixture("callback.cpp", "caller", LAMBDA_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = project.directory.join("callback.click");
    let verify = |source: &str| {
        fs::write(&sidecar, source).unwrap();
        let parsed = read_click_project(&sidecar, source).unwrap();
        verify_program_prepared_project(&parsed, &import).map(|_| parsed)
    };
    let parsed = verify(LAMBDA_SIDECAR).unwrap_or_else(|error| panic!("{}", error.message()));
    for label in ["caller::(lambda#0).contract", "caller.ensures_0"] {
        let expanded =
            expand_project_claim_source_by_label(&parsed, &ProgramInputs::program(&import), label)
                .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import)
            .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
    }
    for (before, after, expected) in [
        (
            "    ensures result == y + y;\n",
            "    ensures result >= y;\n",
            "contract-refinement proof does not establish `Doubling(&caller::(lambda#0))`",
        ),
        (
            "    ensures result == y + y;\n",
            "    ensures result == y + y + 1;\n",
            "contract-refinement proof does not establish `Doubling(&caller::(lambda#0))`",
        ),
        (
            "int caller::(lambda#0)(int y)",
            "int caller::(lambda#1)(int y)",
            "`caller::(lambda#1)` is not a verified or external function compatible with contract `Doubling`",
        ),
    ] {
        let mut hostile = LAMBDA_SIDECAR.replacen(before, after, 1);
        if before == "int caller::(lambda#0)(int y)" {
            hostile = hostile.replace("&caller::(lambda#0)", "&caller::(lambda#1)");
        }
        assert_ne!(hostile, LAMBDA_SIDECAR);
        let Err(error) = verify(&hostile) else {
            panic!("accepted:\n{hostile}");
        };
        let message = click::surface::display_source_names(error.message()).into_owned();
        assert!(message.contains(expected), "{message}");
    }
}

// Lambdas are numbered in source order within their enclosing function.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn cpp_lambdas_are_numbered_in_their_enclosing_function() {
    let project = Project::with_fixture("callback.cpp", "pair", LAMBDA_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "callback.cpp";
contract int Bounded(int x) {
    requires 0 <= x and x <= 1000;
    ensures 0 <= result and result <= 2000;
}
int apply(int (*f)(int), int x) {
    requires Bounded(f);
    requires 0 <= x and x <= 1000;
    ensures 0 <= result and result <= 2000;
}
int pair::(lambda#0)(int y) {
    requires 0 <= y and y <= 1000;
    ensures 0 <= result and result <= 2000;
    ensures result == y + 1;
}
int pair::(lambda#1)(int y) {
    requires 0 <= y and y <= 1000;
    ensures 0 <= result and result <= 2000;
    ensures result == y + y;
}
theorem first_is_bounded() {
    ensures Bounded(&pair::(lambda#0)) by { unfold(Bounded(&pair::(lambda#0))); close(); }
}
theorem second_is_bounded() {
    ensures Bounded(&pair::(lambda#1)) by { unfold(Bounded(&pair::(lambda#1))); close(); }
}
int pair(int x) {
    requires 0 <= x and x <= 1000;
    ensures 0 <= result and result <= 4000;
} by { apply(first_is_bounded()); apply(second_is_bounded()); }
"#;
    let sidecar = project.directory.join("callback.click");
    fs::write(&sidecar, source).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    // Swapping the two contracts makes each lambda's false.
    let swapped = source
        .replacen("ensures result == y + 1;", "ensures result == SWAP;", 1)
        .replacen("ensures result == y + y;", "ensures result == y + 1;", 1)
        .replacen("ensures result == SWAP;", "ensures result == y + y;", 1);
    fs::write(&sidecar, &swapped).unwrap();
    let parsed = read_click_project(&sidecar, &swapped).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

// A lambda converted to a function pointer is admitted in a free function;
// the importer refuses one in a member function by name.
#[test]
fn cpp_lambdas_outside_a_free_function_are_refused() {
    let source = "struct R { int v; int m(int x) noexcept; };\n\
int apply(int (*f)(int) noexcept, int x) noexcept { return f(x); }\n\
int R::m(int x) noexcept { return apply([](int y) noexcept { return y + y; }, x); }\n\
int caller(int x) noexcept { R r{1}; return r.m(x); }\n";
    let project = Project::with_fixture("callback.cpp", "caller", source);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("a C++ lambda is supported only in the body of a free function"),
        "{error}"
    );
}

#[cfg(not(feature = "fast-gate"))]
/// A C++ unit of a project reads an external tree in place, exports two
/// functions of one file into one artifact for one sidecar, and its
/// committed lock still loads after the whole checkout moves.
#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn cpp_project_unit_exports_several_functions_from_an_external_tree() {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let base = std::env::temp_dir().join(format!(
        "click-cpp-unit-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let root = base.join("checkout");
    let source = root.join("vendor/basic/src/pair.cpp");
    fs::create_dir_all(source.parent().unwrap()).unwrap();
    fs::create_dir_all(root.join("proofs/checks")).unwrap();
    let text = "int increment(int& value) noexcept {\n    value = value + 1;\n    return value;\n}\n\nint add_two(int& value) noexcept {\n    increment(value);\n    return increment(value);\n}\n";
    fs::write(&source, text).unwrap();
    fs::write(
        root.join("proofs/checks/pair.click"),
        "verifying \"../../vendor/basic/src/pair.cpp\";\n\
         int32 increment(int32& value) { requires value < 2147483647; owns value; ensures value == old(value) + 1; ensures result == value; }\n\
         int32 add_two(int32& value) { requires value < 2147483646; owns value; ensures value == old(value) + 2; ensures result == value; }\n",
    )
    .unwrap();
    fs::write(
        root.join("proofs/click.project.json"),
        serde_json::json!({"units": {"basic": {
            "language": "c++",
            "root": "../vendor/basic",
            "exceptions": false,
            "rtti": false,
            "args": ["-ffreestanding", "-nostdinc", "-nostdinc++", "-funsigned-char"],
            "sources": {"src/pair.cpp": {"functions": ["increment", "add_two"]}}
        }}})
        .to_string(),
    )
    .unwrap();
    let click = |args: &[&Path]| {
        Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .output()
            .unwrap()
    };
    let output = click(&[Path::new("capture"), &root.join("proofs")]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(fs::read_dir(source.parent().unwrap()).unwrap().count(), 1);
    let output = click(&[
        Path::new("verify"),
        Path::new("--locked"),
        &root.join("proofs/checks/pair.click"),
    ]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("2 selected proofs verified"));

    let moved = base.join("moved");
    fs::rename(&root, &moved).unwrap();
    let sidecar = moved.join("proofs/checks/pair.click");
    let output = click(&[Path::new("verify"), Path::new("--locked"), &sidecar]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );

    fs::write(
        moved.join("vendor/basic/src/pair.cpp"),
        text.replace("+ 1", "+ 2"),
    )
    .unwrap();
    let output = click(&[Path::new("verify"), Path::new("--locked"), &sidecar]);
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(
        !output.status.success() && error.contains("pair.cpp") && error.contains("differs"),
        "{error}"
    );
    let _ = fs::remove_dir_all(&base);
}

const VIRTUAL_SOURCE: &str = "struct Shape { virtual int area(int scale) const noexcept = 0; };
struct Square : Shape {
    int side;
    int area(int scale) const noexcept override { return scale + 1; }
};
int total(const Shape& shape, int scale) noexcept { return shape.area(scale); }
";

// Virtual dispatch is admitted where every override a call may reach is
// imported and checked: a polymorphic class with one polymorphic base,
// reached by reference or built by a constructor that does not read `this`,
// and a call graph whose dispatch edges, from a virtual method to each
// override, close no cycle.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn virtual_dispatch_refuses_construction_recursion_and_other_class_shapes() {
    for (edits, expected) in [
        // Construction without a constructor, and constructors that read
        // `this` while the dynamic type changes or build a nonempty base.
        (
            &[(
                "{ return shape.area(scale); }",
                "{ Square square; square.side = 1; return square.area(scale); }",
            )][..],
            "one public non-default noexcept constructor",
        ),
        (
            &[
                (
                    "    int side;\n",
                    "    int side;\n    explicit Square(int s) noexcept : side(area(s)) {}\n",
                ),
                (
                    "{ return shape.area(scale); }",
                    "{ Square square(scale); return square.area(scale); }",
                ),
            ][..],
            "without reading `this` and has an empty body",
        ),
        (
            &[
                (
                    "    int side;\n",
                    "    int side;\n    explicit Square(int s) noexcept : side(s) { side = s; }\n",
                ),
                (
                    "{ return shape.area(scale); }",
                    "{ Square square(scale); return square.area(scale); }",
                ),
            ][..],
            "without reading `this` and has an empty body",
        ),
        (
            &[
                ("= 0; };", "= 0;\n    Shape() noexcept {}\n};"),
                (
                    "    int side;\n",
                    "    int side;\n    explicit Square(int s) noexcept : side(s) {}\n",
                ),
                (
                    "{ return shape.area(scale); }",
                    "{ Square square(scale); return square.area(scale); }",
                ),
            ][..],
            "names its base's own non-default constructor in its initializer list",
        ),
        // The explicit void-cast statement is refused during export before
        // the destructor-shape check.
        (
            &[(
                "= 0; };",
                "= 0;\n    virtual ~Shape() noexcept { int unused = 0; (void)unused; }\n};",
            )][..],
            "unsupported statement in the first C++ slice",
        ),
        // A base destructor that runs supported code, under a class with no
        // destructor of its own to run it from.
        (
            &[(
                "= 0; };",
                "= 0;\n    virtual ~Shape() noexcept { int unused = 0; }\n};",
            )][..],
            "runs after it only its base's written destructor or nothing",
        ),
        // A call back through the interface from an override.
        (
            &[
                (
                    "= 0; };",
                    "= 0;\n    int twice(int scale) const noexcept { return area(scale); }\n};",
                ),
                ("return scale + 1; }", "return twice(scale); }"),
            ][..],
            "recursive C++ calls are outside the supported slice",
        ),
        (
            &[(
                "return shape.area(scale); }",
                "return shape.Shape::area(scale); }",
            )][..],
            "unsupported C++ method dispatch",
        ),
        (
            &[(
                "struct Square : Shape {",
                "struct Other { virtual int other() const noexcept { return 1; } };\nstruct Square : Shape, Other {",
            )][..],
            "at most one public non-virtual base",
        ),
        (
            &[(
                "= 0; };",
                "= 0; };\nint Shape::area(int scale) const noexcept { return scale; }",
            )][..],
            "pure virtual C++ method with a definition",
        ),
    ] {
        let mut source = VIRTUAL_SOURCE.to_string();
        for (from, to) in edits {
            assert!(source.contains(from), "{from}");
            source = source.replacen(from, to, 1);
        }
        let project = Project::with_fixture("shapes.cpp", "total", &source);
        let error = refresh_import(&project.config())
            .and_then(|_| load_import(&project.config()).map(|_| ()))
            .unwrap_err();
        assert!(error.contains(expected), "{error}");
    }
    // An override the sidecar does not state is never verified, so the
    // interface may not stand for it.
    let project = Project::with_fixture("shapes.cpp", "total", VIRTUAL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let error = ProgramVerificationSession::new_program_prepared(
        r#"verifying "shapes.cpp";
extern int Shape::area(int scale) const {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result;
}
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 1000;
    ensures scale < result;
}
"#,
        &import,
    )
    .err()
    .expect("an unstated override must be refused");
    let rendered = click::surface::display_source_names(&format!("{error:?}")).into_owned();
    assert!(
        rendered.contains(
            "`Square::area` overrides the virtual method `Shape::area` but has no contract"
        ),
        "{rendered}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: C++ object-state obligation expansion and cold replay"]
fn bound_class_object_call_obligations_expand_and_cold_replay() {
    for name in [
        "cpp_class_object_state.md",
        "cpp_class_object_state_mutable.md",
        "cpp_class_object_state_mutable_this_calls.md",
        "cpp_class_subclass_override_keeps_the_interface.md",
        "cpp_class_const_reference_keeps_fields.md",
        "cpp_polymorphic_base_construction.md",
        "cpp_class_subclass_local_object_packs_itself.md",
        "cpp_polymorphic_local_construction.md",
        "cpp_polymorphic_virtual_destructor.md",
    ] {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(name);
        let text = fs::read_to_string(&path).unwrap();
        let fixture = parse_mdtest(&path, &text).unwrap();
        let cpp = fixture.cpp_source.unwrap();
        let source = fixture.click_source.unwrap();
        let project = Project::with_fixture(&cpp.filename, &cpp.functions[0], &cpp.source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        // Naming the pack's output is sufficient: the ordinary call-obligation
        // solver proves its model-field bounds, without an extra written have.
        assert!(source.contains("object_resource(): packed"));
        assert!(!source.contains("have "));
        let parsed = read_click_project(&path, &source).unwrap();
        let (session, verified) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let expanded = click::surface::expand_verified_function_claim_source_by_label(
            &source,
            &verified,
            "caller.contract",
        )
        .unwrap()
        .expect("the caller's written proof has a certificate");
        assert!(expanded.contains("object_resource(): packed"), "{expanded}");
        let rewritten = parsed.with_entry_source(expanded.clone());
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            "caller.contract",
            0,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .expect("the bound object certificate must verify retained");
        drop(session);
        verify_program_prepared_project(&rewritten, &import)
            .expect("the bound object certificate must verify cold");
    }
}

// An override of a method of a class whose object carries state, or of a
// defining class's method, is stated on its own class's memory, so its class
// defines that state; and a class deriving from a defining class overrides
// each of its methods stated on that class's memory.
#[test]
fn class_object_state_refuses_undefined_overrides_and_inherited_methods() {
    let source = "struct Shape { virtual int area(int scale) const noexcept = 0; };
struct Square : Shape {
    int side;
    int color;
    int area(int scale) const noexcept override { return side + scale; }
};
struct Tile : Square {
    int area(int scale) const noexcept override { return scale + side; }
};
int total(const Shape& shape, int scale) noexcept { return shape.area(scale); }
";
    let sidecar = r#"verifying "shapes.cpp";
class Shape {
    function size(this) -> int32;
}
extern int Shape::area(int scale) const {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(this) and size(this) <= 100;
    ensures result == size(this) + scale;
}
class Square : Shape {
    function size(this) -> int32 { this->side }
}
int Square::area(int scale) const {
}
int Tile::area(int scale) const {
}
int total(const Shape& shape, int scale) {
    requires 0 <= scale and scale <= 100;
    requires 0 <= size(shape) and size(shape) <= 100;
    ensures result == size(shape) + scale;
}
"#;
    let project = Project::with_fixture("shapes.cpp", "total", source);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    for (from, to, expected) in [
        (
            "",
            "",
            "`Tile::area` overrides `Square::area`, a method of a class that defines its \
             object's state",
        ),
        (
            "class Square : Shape {\n    function size(this) -> int32 { this->side }\n}\n",
            "",
            "`Square::area` overrides `Shape::area`, whose class's object carries state",
        ),
        (
            "int Tile::area(int scale) const {\n}\n",
            "class Tile : Square {\n}\n",
            "`Tile::area` overrides the virtual method `Square::area` but has no contract",
        ),
    ] {
        let sidecar = sidecar.replacen(from, to, 1);
        let error = ProgramVerificationSession::new_program_prepared(&sidecar, &import)
            .err()
            .expect("the override must be refused");
        let rendered = click::surface::display_source_names(&format!("{error:?}")).into_owned();
        assert!(rendered.contains(expected), "{rendered}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: C++ imports and whole-claim retained/cold certificate checks"]
fn class_bool_member_whole_certificate_preserves_every_return_case() {
    let source = include_str!("fixtures/cpp-verification/class-record/class_record.cpp");
    let sidecar = include_str!("fixtures/cpp-verification/class-record/is_empty.click");
    for (access, locked_header) in [
        ("private:", false),
        ("protected:", false),
        ("", false),
        ("private:", true),
    ] {
        let header_sidecar;
        let (project, sidecar) = if locked_header {
            header_sidecar = sidecar.replace("class_record.cpp", "header_record.cpp");
            (
                header_record_project("FeeRateState::IsEmpty"),
                header_sidecar.as_str(),
            )
        } else {
            (
                Project::with_fixture(
                    "class_record.cpp",
                    "FeeRateState::IsEmpty",
                    &source.replace("private:", access),
                ),
                sidecar,
            )
        };
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let path = project.directory.join("original.click");
        fs::write(&path, sidecar).unwrap();
        let parsed = read_click_project(&path, sidecar).unwrap();
        let inputs = ProgramInputs::program(&import);
        let sites = project_smart_tactic_source_sites(&parsed, &inputs).unwrap();
        let claim = sites[0].claim_label.clone();
        let (session, verified) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let expanded = click::surface::expand_verified_function_claim_source_by_label(
            sidecar, &verified, &claim,
        )
        .unwrap()
        .expect("the checked claim is declared in the original source");
        assert!(expanded.contains("if old(this->size) == 0 {"), "{expanded}");
        assert!(!expanded.contains("this[2]"), "{expanded}");
        let rewritten = parsed.with_entry_source(expanded.clone());
        let position = project_tactic_source_position(&rewritten, &inputs, &claim, 0).unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .expect("the complete certificate verifies retained");
        drop(session);
        verify_program_prepared_project(&rewritten, &import)
            .expect("the complete certificate verifies cold");
    }
}

// A diagnostic prints a record by its C++ path, the instance Clang prints,
// not by the layout name the importer records for it.
#[test]
fn diagnostics_print_record_types_by_their_cpp_paths() {
    let project = Project::with_fixture("instances.cpp", "both", CLASS_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let swapped = "verifying \"instances.cpp\"; int32 both(const Box<WeightTag, true>& left, const Box<SizeTag, true>& right) { views left.value; ensures result == left.value; }";
    fs::write(project.directory.join("bad.click"), swapped).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), swapped).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("the swapped record types are refused");
    let shown = click::surface::display_source_names(&error.to_string()).into_owned();
    assert!(
        shown.contains(
            ".click has const Box<WeightTag, true>& left, C has const Box<SizeTag, true>& left"
        ),
        "{shown}"
    );
    let unknown_field = "verifying \"instances.cpp\"; int32 both(const Box<SizeTag, true>& left, const Box<WeightTag, true>& right) { views left.value; ensures result == left.nope; }";
    fs::write(project.directory.join("bad.click"), unknown_field).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), unknown_field).unwrap();
    let error =
        verify_program_prepared_project(&parsed, &import).expect_err("the field does not exist");
    let shown = click::surface::display_source_names(&error.to_string()).into_owned();
    assert!(
        shown.contains("`Box<SizeTag, true>` has no field `nope`"),
        "{shown}"
    );
}

// `p->field` reads through a record pointer held by a parameter or local.
// A pointer read from a field or returned by a call does not root a place,
// and a pointer to a polymorphic record is not a simple record pointer.
#[test]
fn record_pointer_arrows_require_a_parameter_or_local_root() {
    let node = "struct Node { int value; Node* next; };\nNode* rest(Node* n) noexcept { return n->next; }\n";
    for (name, body, expected) in [
        (
            "field",
            "int probe(Node* n) noexcept { return n->next->value; }",
            "arrow access requires the current object or a record pointer parameter or local",
        ),
        (
            "call",
            "int probe(Node* n) noexcept { return rest(n)->value; }",
            "arrow access requires the current object or a record pointer parameter or local",
        ),
        (
            "polymorphic",
            "struct Shape { virtual int area() noexcept = 0; };\nint probe(Shape* s) noexcept { return 0; }",
            "a mutable pointer to a simple record",
        ),
    ] {
        let source = format!("{node}{body}\n");
        let project = Project::with_fixture("list.cpp", "probe", &source);
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
    }
}

// `new` allocates one simple aggregate record with the global `operator new`,
// initialized one field per brace initializer, and `delete` ends one; array
// forms and placement are refused.
#[test]
fn new_and_delete_admit_one_simple_record() {
    let node = "struct Node { int value; Node* next; };\n";
    for (name, body, expected) in [
        (
            "array_new",
            "int probe() noexcept { Node* n = nullptr; n = new Node[2]; return 0; }",
            "a supported C++ `new` allocates one simple aggregate record",
        ),
        (
            "partial_initializer",
            "int probe() noexcept { Node* n = nullptr; n = new Node{1}; return 0; }",
            "one direct brace initializer per field",
        ),
        (
            "array_delete",
            "int probe(Node* n) noexcept { delete[] n; return 0; }",
            "a supported C++ `delete` ends one simple record",
        ),
    ] {
        let source = format!("{node}{body}\n");
        let project = Project::with_fixture("list.cpp", "probe", &source);
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
    }
}

// A default member initializer is a constant, and a local default-constructed
// from them needs one on every field; other forms stay refused.
#[test]
fn default_construction_reads_constant_member_initializers_only() {
    for (name, source, expected) in [
        (
            "computed",
            "int seed() noexcept { return 3; }\nstruct S { int a = seed(); };\nint probe() noexcept { S s; return s.a; }",
            "the supported C++ record fields must be",
        ),
        (
            "missing",
            "struct S { int a = 1; int b; };\nint probe() noexcept { S s; return s.a; }",
            "one direct brace initializer per field",
        ),
    ] {
        let source = format!("{source}\n");
        let project = Project::with_fixture("init.cpp", "probe", &source);
        let error = refresh_import(&project.config())
            .expect_err(&format!("{name} must not enter a locked artifact"));
        assert!(error.contains(expected), "{name}: {error}");
    }
}

/// A Click home with the C++ front end installed beside this version, as
/// `click add cpp` places it, holding `exporter`.
#[cfg(not(feature = "fast-gate"))]
fn installed_cpp_home(name: &str, exporter: &Path) -> PathBuf {
    let home = scratch_copy(name);
    let frontend = home
        .join("versions")
        .join(env!("CARGO_PKG_VERSION"))
        .join("frontends/cpp");
    fs::create_dir_all(&frontend).unwrap();
    fs::copy(exporter, frontend.join("click-cpp-exporter")).unwrap();
    home
}

/// The installed `click`, run with only `home`: no exporter override and
/// nothing on `PATH`.
#[cfg(not(feature = "fast-gate"))]
fn installed_click(home: &Path, project: &Path, args: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_click"))
        .args(args)
        .current_dir(project)
        .env("CLICK_HOME", home)
        .env("CLICK_NO_VERSION_DISPATCH", "1")
        .env("PATH", "")
        .env("HOME", home.join("empty-home"))
        .env_remove("CLICK_CPP_EXPORTER")
        .env_remove("LD_LIBRARY_PATH")
        .output()
        .unwrap()
}

/// A copy of the committed `example`, outside the repository, without its
/// lock and artifacts.
#[cfg(not(feature = "fast-gate"))]
fn unlocked_copy(example: &str, name: &str) -> PathBuf {
    let copy = scratch_copy(name);
    copy_tree(&Path::new(env!("CARGO_MANIFEST_DIR")).join(example), &copy);
    fs::remove_dir_all(copy.join(".click")).unwrap();
    copy
}

#[cfg(not(feature = "fast-gate"))]
/// Without an installed front end, `click capture` says how to install
/// one; an installed exporter that is not the pinned one is refused before
/// it exports anything. Neither writes a lock.
#[test]
fn an_installed_cpp_front_end_is_required_and_checked() {
    let version = env!("CARGO_PKG_VERSION");
    let project = unlocked_copy("examples/basic-cpp", "installed-refusals");
    let empty = scratch_copy("installed-empty-home");
    let missing = installed_click(&empty, &project, &["capture"]);
    let stderr = String::from_utf8_lossy(&missing.stderr);
    assert!(!missing.status.success());
    assert!(
        stderr.contains(&format!(
            "the C++ front end is not installed for Click {version}"
        )) && stderr.contains("click add cpp"),
        "{stderr}"
    );

    let impostor = scratch_copy("installed-impostor");
    let script = impostor.join("click-cpp-exporter");
    fs::write(
        &script,
        "#!/bin/sh\necho 'click-cpp-exporter 0; schema 1; clang clang version 18.1.8'\n",
    )
    .unwrap();
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&script, fs::Permissions::from_mode(0o755)).unwrap();
    }
    let home = installed_cpp_home("installed-wrong-version", &script);
    let refused = installed_click(&home, &project, &["capture"]);
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(!refused.status.success());
    assert!(
        stderr.contains("C++ exporter version mismatch; expected click-cpp-exporter"),
        "{stderr}"
    );
    assert!(!project.join(click::project::LOCK_NAME).exists());
    for directory in [project, empty, impostor, home] {
        let _ = fs::remove_dir_all(directory);
    }
}

#[cfg(not(feature = "fast-gate"))]
/// The installed layout alone prepares and verifies the C++ demonstrations:
/// with the pinned exporter installed beside this Click, no override and
/// nothing on `PATH`, locking `examples/basic-cpp`, `examples/multifile-cpp`
/// and the hermetic `MoneyRange` integration outside the repository writes their committed
/// locks and artifacts byte for byte, and their sidecars verify.
#[test]
#[ignore = "nightly: locks three projects with the pinned exporter"]
fn the_installed_cpp_front_end_reproduces_the_committed_imports() {
    let exporter = PathBuf::from(
        std::env::var_os("CLICK_CPP_EXPORTER")
            .expect("scripts/check.sh supplies the pinned C++ exporter"),
    );
    let home = installed_cpp_home("installed-home", &exporter);
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let money_range = "integrations/bitcoin-core-money-range";
    for (example, sidecars) in [
        (
            "examples/basic-cpp",
            &[
                "increment.click",
                "with_restore.click",
                "with_restore_caller.click",
            ][..],
        ),
        (money_range, &["MoneyRange.click"][..]),
        ("examples/multifile-cpp", &["counter.click"][..]),
    ] {
        let project = unlocked_copy(example, "installed-project");
        if example == money_range {
            let closure = root.join(money_range).join("input-closure.tar.gz");
            let unpacked = Command::new("tar")
                .arg("-xzf")
                .arg(&closure)
                .arg("-C")
                .arg(&project)
                .status()
                .unwrap();
            assert!(unpacked.success(), "extract {}", closure.display());
        }
        let locked = installed_click(&home, &project, &["capture"]);
        assert!(
            locked.status.success(),
            "{example}: {}",
            String::from_utf8_lossy(&locked.stderr)
        );
        let committed = root.join(example);
        let mut files = vec![PathBuf::from(click::project::LOCK_NAME)];
        let mut pending = vec![PathBuf::from(".click")];
        while let Some(relative) = pending.pop() {
            for entry in fs::read_dir(committed.join(&relative)).unwrap() {
                let entry = entry.unwrap();
                let child = relative.join(entry.file_name());
                if entry.file_type().unwrap().is_dir() {
                    pending.push(child);
                } else {
                    files.push(child);
                }
            }
        }
        for file in files {
            assert_eq!(
                fs::read(project.join(&file)).unwrap(),
                fs::read(committed.join(&file)).unwrap(),
                "{example}: {}",
                file.display()
            );
        }
        for sidecar in sidecars {
            let verified = installed_click(&home, &project, &["verify", sidecar]);
            assert!(
                verified.status.success(),
                "{example} {sidecar}: {}",
                String::from_utf8_lossy(&verified.stderr)
            );
        }
        let _ = fs::remove_dir_all(project);
    }
    let _ = fs::remove_dir_all(home);
}

/// A call to a project function another translation unit defines exports
/// the callee's interface only, marked external. The caller verifies against
/// a contract its sidecar states and is refused without one.
#[test]
fn a_call_into_another_translation_unit_is_checked_against_a_contract() {
    let project = Project::with_fixture(
        "a.cpp",
        "add_two",
        "#include \"b.h\"\nint add_two(int value) noexcept {\n    int once = add_one(value);\n    return add_one(once);\n}\n",
    );
    fs::write(
        project.directory.join("b.h"),
        "int add_one(int value) noexcept;\n",
    )
    .unwrap();
    let project_file = project.directory.join(click::project::FILE_NAME);
    fs::write(
        &project_file,
        serde_json::json!({"units": {"demo": {
            "language": "c++",
            "args": ["-ffreestanding", "-nostdinc", "-nostdinc++"],
            "sources": {"a.cpp": {"functions": ["add_two"], "dependencies": ["b.h"]}},
        }}})
        .to_string(),
    )
    .unwrap();
    click::project::Project::load(&project_file)
        .and_then(|unit| unit.lock_with_cpp_exporter(Some(&project.exporter)))
        .unwrap();
    let artifact: serde_json::Value = serde_json::from_slice(
        &fs::read(
            project
                .directory
                .join(".click/captures/demo/a.cpp.click-cpp.json"),
        )
        .unwrap(),
    )
    .unwrap();
    let callee = &artifact["reachable_functions"][0];
    assert_eq!(callee["name"], "add_one", "{artifact}");
    assert_eq!(callee["external"], true, "{artifact}");
    assert_eq!(callee["body"], serde_json::json!([]), "{artifact}");
    let source = project.directory.join("a.cpp");
    let import = match click::project::Project::load(&project_file)
        .unwrap()
        .prepared_sources(&[("a.cpp".into(), fs::canonicalize(&source).ok())])
        .unwrap()
    {
        Some(click::project::UnitSelection::Program(click::languages::PreparedProgram::Cpp(
            import,
        ))) => import,
        _ => panic!("expected the prepared C++ unit"),
    };
    let caller =
        "int32 add_two(int32 value) {\n requires value < 50;\n ensures result == value + 2;\n}\n";
    let contract = "extern int32 add_one(int32 value) {\n requires value < 100;\n ensures result == value + 1;\n}\n";
    let path = project.directory.join("a.click");
    let with_contract = format!("verifying \"a.cpp\";\n{contract}{caller}");
    fs::write(&path, &with_contract).unwrap();
    verify_program_prepared_project(&read_click_project(&path, &with_contract).unwrap(), &import)
        .unwrap();
    let without = format!("verifying \"a.cpp\";\n{caller}");
    let error =
        verify_program_prepared_project(&read_click_project(&path, &without).unwrap(), &import)
            .unwrap_err();
    assert!(error.to_string().contains("add_one"), "{error}");
}

#[cfg(not(feature = "fast-gate"))]
/// A sidecar that verifies several sources of one C++ unit links them
/// (`examples/multifile-cpp`). A call whose callee neither a linked source
/// defines nor the sidecar states a contract for is refused, and so are two
/// sources that define one function differently.
#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn linked_cpp_sources_refuse_an_unproved_callee_and_differing_definitions() {
    let exporter = PathBuf::from(
        std::env::var_os("CLICK_CPP_EXPORTER")
            .expect("scripts/check.sh supplies the pinned C++ exporter"),
    );
    let project = scratch_copy("linked");
    copy_tree(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/multifile-cpp"),
        &project,
    );
    fs::write(
        project.join("conflict.cpp"),
        "int counter_add(int& counter, int amount) noexcept {\n    counter = counter + amount + 1;\n    return counter;\n}\n",
    )
    .unwrap();
    let project_file = project.join(click::project::FILE_NAME);
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(&project_file).unwrap()).unwrap();
    config["units"]["counters"]["sources"]["conflict.cpp"] =
        serde_json::json!({"functions": ["counter_add"]});
    fs::write(&project_file, config.to_string()).unwrap();
    click::project::Project::load(&project_file)
        .and_then(|unit| unit.lock_with_cpp_exporter(Some(&exporter)))
        .unwrap();
    let verify = |name: &str, source: &str| {
        let path = project.join(name);
        fs::write(&path, source).unwrap();
        Command::new(env!("CARGO_BIN_EXE_click"))
            .args(["verify", name])
            .current_dir(&project)
            .env_remove("CLICK_CPP_EXPORTER")
            .output()
            .unwrap()
    };
    let sidecar = fs::read_to_string(project.join("counter.click")).unwrap();
    let linked = verify("counter.click", &sidecar);
    assert!(
        linked.status.success(),
        "{}",
        String::from_utf8_lossy(&linked.stderr)
    );

    // Verifying the client alone leaves `counter_add` without a definition
    // or a contract.
    let client = "verifying \"client.cpp\";\n\
                  int counter_limit() { ensures result == 1000; }\n\
                  int bump_then_double(int& counter) {\n requires 0 <= counter and counter <= 50;\n owns counter;\n ensures result == counter + 1000;\n}\n";
    let unproved = verify("client.click", client);
    let stderr = String::from_utf8_lossy(&unproved.stderr);
    assert!(!unproved.status.success());
    assert!(stderr.contains("`counter_add`"), "{stderr}");

    let conflicting = sidecar.replace(
        "verifying \"client.cpp\";",
        "verifying \"client.cpp\";\nverifying \"conflict.cpp\";",
    );
    let refused = verify("conflict.click", &conflicting);
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(!refused.status.success());
    assert!(
        stderr.contains("define `counter_add` differently"),
        "{stderr}"
    );
    let _ = fs::remove_dir_all(project);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: native-interface unwritten reference entry and caller checks"]
fn cpp_native_interface_reference_binding_does_not_initialize_storage_offline() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/cpp-verification/native-interface");
    let cpp = fs::read_to_string(fixture.join("reference.cpp")).unwrap();
    let proof = fs::read_to_string(fixture.join("reference.click")).unwrap();
    for (name, cpp, accepted) in [
        ("write", cpp.clone(), true),
        (
            "bind",
            cpp.replace("alias = 7;", "")
                .replace("return value;\n}", "return 7;\n}"),
            true,
        ),
        ("read", cpp.replace("alias = 7;", ""), false),
    ] {
        let project = Project::with_fixture("interface.cpp", "probe", &cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        if accepted {
            check_selected_claim_certificate(&project, &import, &proof);
        } else {
            let path = project.directory.join("bad.click");
            fs::write(&path, &proof).unwrap();
            let parsed = read_click_project(&path, &proof).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).expect_err(name);
            assert!(error.message().contains("uninitialized"), "{error}");
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: native-interface record-copy input initialization and caller authority"]
fn cpp_native_interface_record_copy_checks_every_source_field_offline() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/cpp-verification/native-interface");
    let cpp = fs::read_to_string(fixture.join("copy.cpp")).unwrap();
    let proof = fs::read_to_string(fixture.join("copy.click")).unwrap();
    let project = Project::with_fixture("interface.cpp", "probe", &cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_selected_claim_certificate(&project, &import, &proof);
    for invalid in [
        proof.replace("views source.unused;", "owns uninitialized(source.unused);"),
        proof.replace("views source.unused;", ""),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &invalid).unwrap();
        let parsed = read_click_project(&path, &invalid).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).expect_err("copy input");
        assert_eq!(
            error.kind(),
            click::surface::ClickErrorKind::Proof,
            "{error}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: C++ by-value record witness proof and replay"]
fn cpp_by_value_record_carries_a_contract_value() {
    let project = Project::with_fixture(
        "by-value.cpp",
        "probe",
        r#"struct View { int* data; unsigned long count; };
unsigned long shorten(View value) noexcept {
    unsigned long original = value.count;
    value.count = 0;
    return original;
}
unsigned long probe(const View& source) noexcept { return shorten(source); }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "by-value.cpp";
abstract resource view_state(s: const struct View*) { field count: uint64; }
uint64 shorten(struct View value) {
    let count: uint64;
    requires value.count == count;
    ensures result == count;
}
uint64 probe(const struct View& source) {
    owns state: view_state(&source);
    views source.data;
    views source.count;
    requires source.count == state.count;
    ensures result == old(state.count);
    ensures source.count == old(source.count);
    ensures source.data == old(source.data);
    ensures state.count == old(state.count);
} by {
    step(shorten, { count: old(source.count) });
}
"#;
    let sidecar = project.directory.join("by-value.click");
    fs::write(&sidecar, proof).unwrap();
    let parsed = read_click_project(&sidecar, proof).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();

    let invalid = proof.replace("count: old(source.count)", "count: 0u64");
    let sidecar = project.directory.join("wrong-value.click");
    fs::write(&sidecar, &invalid).unwrap();
    let parsed = read_click_project(&sidecar, &invalid).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("a different count does not describe the copied value");
    assert!(error.message().contains("precondition"), "{error:?}");

    project.write_config("shorten");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let (callee, _) = proof.split_once("uint64 probe(").unwrap();
    fs::write(&sidecar, callee).unwrap();
    let parsed = read_click_project(&sidecar, callee).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
}

#[test]
fn cpp_by_value_record_keeps_receiver_field_ownership_at_proof_entry() {
    let project = Project::with_fixture(
        "reader.cpp",
        "Reader::read",
        r#"struct Field { unsigned long first; unsigned long count; };
struct Reader {
    Field data;
    void read(Field dst) noexcept { return; }
};
void caller(Reader& reader, Field dst) noexcept { reader.read(dst); }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let path = project.directory.join("reader.click");
    let callee = r#"verifying "reader.cpp";
void Reader::read(Field dst) {
    owns this->data.first;
    ensures true;
}
"#;
    fs::write(&path, callee).unwrap();
    let parsed = read_click_project(&path, callee).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();

    project.write_config("caller");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let caller = format!(
        "{callee}void caller(Reader& reader, Field dst) {{\n    owns reader.data.first;\n    ensures true;\n}}\n"
    );
    fs::write(&path, &caller).unwrap();
    let parsed = read_click_project(&path, &caller).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();

    let caller = caller.replace("owns reader.data.first;", "views reader.data.first;");
    let parsed = read_click_project(&path, &caller).unwrap();
    let error = verify_program_prepared_project(&parsed, &import)
        .expect_err("the caller only has read access to the receiver field");
    let report = error.report();
    assert!(report.contains("`caller.ensures_0`"), "{report}");
    assert!(report.contains("write ownership required"), "{report}");
}

const RECORD_TEMPORARY_ARGUMENT_SOURCE: &str = r#"
struct Value {
    int value;
    explicit Value(int input) noexcept : value(input) {}
};
Value convert(Value source) noexcept { return Value{source.value}; }
struct Sink {
    int total;
    void put(Value input) noexcept { total = input.value; }
};
template<class Stream> void feed(Stream& sink, int input) noexcept {
    sink.put(convert(Value{input}));
}
int probe(Sink& sink, int input) noexcept {
    feed(sink, input);
    return sink.total;
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: nonthrowing record prvalue arguments and template stream"]
fn record_prvalue_arguments_construct_forward_and_end_at_the_full_expression() {
    let project =
        Project::with_fixture("record-args.cpp", "probe", RECORD_TEMPORARY_ARGUMENT_SOURCE);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let feed_path = &import
        .export()
        .reachable_functions
        .iter()
        .find(|function| function.name.starts_with("feed__record_"))
        .unwrap()
        .path;
    let feed_name = click::languages::cpp::names::path_name(feed_path);
    let feed = lowered
        .reachable_kernel_functions()
        .iter()
        .find(|function| function.name() == feed_name)
        .unwrap();
    fn ends(statement: &click::kernel::ProgramStatement, result: &mut Vec<Vec<String>>) {
        match statement {
            click::kernel::ProgramStatement::Seq(statements) => {
                for statement in statements.iter() {
                    ends(statement, result);
                }
            }
            click::kernel::ProgramStatement::EndAutomaticLifetimes { names, .. } => {
                result.push(names.iter().map(ToString::to_string).collect())
            }
            _ => {}
        }
    }
    let mut endings = Vec::new();
    ends(feed.body(), &mut endings);
    assert!(
        endings.iter().any(|names| names.len() == 2),
        "both argument temporaries end together: {endings:?}"
    );
    let source = r#"verifying "record-args.cpp";
Value::Value(int32 input) {
    owns this->value;
    ensures this->value == input;
}
struct Value convert(struct Value source) {
    ensures result.value == old(source.value);
}
void Sink::put(struct Value input) {
    owns this->total;
    ensures this->total == old(input.value);
}
void feed<Sink>(struct Sink& sink, int32 input) {
    owns sink.total;
    ensures sink.total == input;
}
int32 probe(struct Sink& sink, int32 input) {
    owns sink.total;
    ensures sink.total == input;
    ensures result == input;
}
"#;
    check_return_call_sidecar(&project, &import, source);
    // Expand each source body, including the temporary-bearing helper,
    // and replay one proof edit per retained session's source boundary.
    let sidecar = project.directory.join("arithmetic.click");
    let parsed = read_click_project(&sidecar, source).unwrap();
    let labels = import
        .export()
        .functions
        .iter()
        .chain(&import.export().reachable_functions)
        .map(|function| {
            format!(
                "{}.ensures_0",
                click::languages::cpp::names::path_name(&function.path)
            )
        })
        .collect::<Vec<_>>();
    let mut expanded = source.to_owned();
    let mut rewritten = parsed.with_entry_source(expanded.clone());
    for label in &labels {
        let baseline = rewritten;
        expanded = expand_project_claim_source_by_label(
            &baseline,
            &ProgramInputs::program(&import),
            label,
        )
        .unwrap_or_else(|error| panic!("{label}: {}", error.report()));
        rewritten = parsed.with_entry_source(expanded.clone());
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&baseline, &import).unwrap();
        let position =
            project_tactic_source_position(&rewritten, &ProgramInputs::program(&import), label, 0)
                .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap_or_else(|error| panic!("{label}: {}", error.report()));
    }
    click::surface::without_implicit_solve(|| verify_program_prepared_project(&rewritten, &import))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.report()));
    assert!(!expanded.contains(".temporary("), "{expanded}");
    let explicit_materialization = source.replace(
        "    ensures sink.total == input;\n}\nint32 probe(",
        "    ensures sink.total == input;\n} by {\n    step_until(call(0).entry);\n    have byte_offset(region(0).result, 0) == region(0).result;\n    step(); step();\n    have region(0).result == region(2).result;\n    have region(2).result.value == input;\n}\nint32 probe(",
    );
    assert_ne!(explicit_materialization, source);
    let explicit_project = parsed.with_entry_source(explicit_materialization);
    verify_program_prepared_project(&explicit_project, &import)
        .expect("cite the object materialized by the void constructor");
    let false_value = source.replace("ensures result == input;", "ensures result == 7;");
    let sidecar = project.directory.join("false.click");
    fs::write(&sidecar, &false_value).unwrap();
    let parsed = read_click_project(&sidecar, &false_value).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: record temporary argument source admission controls"]
fn record_temporary_arguments_refuse_storage_observation_unwinding_and_copy_returns() {
    for (name, source, diagnostic) in [
        (
            "self-address",
            RECORD_TEMPORARY_ARGUMENT_SOURCE
                .replace("int value;", "int* self; int value;")
                .replace(": value(input)", ": self(&value), value(input)")
                .replace(
                    "sink.put(convert(Value{input}));",
                    "sink.put(Value{input});",
                ),
            "temporary constructor must preserve argument values",
        ),
        (
            "throwing-consumer",
            RECORD_TEMPORARY_ARGUMENT_SOURCE
                .replace("void put(Value input) noexcept", "void put(Value input)"),
            "record temporary calls require a nonthrowing callee",
        ),
        (
            "copy-return",
            RECORD_TEMPORARY_ARGUMENT_SOURCE
                .replace("return Value{source.value};", "return source;"),
            "record return requires a resolved trivial lvalue copy",
        ),
    ] {
        let project = Project::with_fixture(&format!("{name}.cpp"), "probe", &source);
        if name == "throwing-consumer" {
            project.write_exception_enabled_compilation_database();
            project.write_config_with_profile("probe", &format!("{name}.cpp"), true);
        }
        let result = refresh_import(&project.config())
            .and_then(|_| load_import(&project.config()).map(|_| ()));
        let error = result.expect_err(name);
        assert!(error.contains(diagnostic), "{name}: {error}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: nominal record function-template arguments"]
fn record_function_template_arguments_preserve_nominal_identity_offline() {
    let source = "namespace left { struct Stream { int value; }; } struct left_Stream { int value; }; template<class T> int read(T& stream) noexcept { return stream.value; } int probe(left::Stream& a, left_Stream& b) noexcept { int first = read(a); int second = read(b); return first + second; }";
    let project = Project::with_fixture("record-template.cpp", "probe", source);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let instances = import
        .export()
        .reachable_functions
        .iter()
        .filter(|function| function.name.starts_with("read__record_"))
        .collect::<Vec<_>>();
    assert_eq!(instances.len(), 2);
    assert_ne!(instances[0].name, instances[1].name);
    assert_ne!(instances[0].declaration_id, instances[1].declaration_id);
    let proof = r#"verifying "record-template.cpp";
int32 read<left::Stream>(struct Stream& stream) { views stream.value; ensures result == stream.value; }
int32 read<left_Stream>(struct left_Stream& stream) { views stream.value; ensures result == stream.value; }
int32 probe(struct Stream& a, struct left_Stream& b) {
    requires a.value == 3; requires b.value == 5;
    views a.value; views b.value;
    ensures result == 8;
}
"#;
    check_return_call_sidecar(&project, &import, proof);
}

// Frozen project imports must advance with the exporter just as mdtests do.
// The release installation test independently checks the basic example.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: regenerate committed C++ project imports with the pinned exporter"]
fn committed_cpp_project_imports_match_the_pinned_exporter() {
    fn copy_tree(from: &Path, to: &Path) {
        fs::create_dir_all(to).unwrap();
        for entry in fs::read_dir(from).unwrap() {
            let entry = entry.unwrap();
            let target = to.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                copy_tree(&entry.path(), &target);
            } else {
                fs::copy(entry.path(), target).unwrap();
            }
        }
    }
    fn files(root: &Path, relative: &Path, output: &mut Vec<PathBuf>) {
        for entry in fs::read_dir(root.join(relative)).unwrap() {
            let entry = entry.unwrap();
            let path = relative.join(entry.file_name());
            if entry.file_type().unwrap().is_dir() {
                files(root, &path, output);
            } else {
                output.push(path);
            }
        }
    }
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let exporter = PathBuf::from(std::env::var_os("CLICK_CPP_EXPORTER").unwrap());
    let refresh = std::env::var("CLICK_REFRESH_CPP_IMPORTS").is_ok_and(|value| value == "1");
    for relative in [
        "examples/basic-cpp",
        "examples/cpp-stack",
        "examples/multifile-cpp",
        "examples/integer-languages/cpp",
        "integrations/bitcoin-core-money-range",
    ] {
        let committed = root.join(relative);
        let temporary = tempfile::tempdir().unwrap();
        let prepared = temporary.path();
        copy_tree(&committed, prepared);
        if prepared.join("input-closure.tar.gz").is_file() {
            assert!(
                std::process::Command::new("tar")
                    .args(["-xzf", "input-closure.tar.gz"])
                    .current_dir(prepared)
                    .status()
                    .unwrap()
                    .success()
            );
        }
        click::project::Project::load(&prepared.join(click::project::FILE_NAME))
            .and_then(|project| project.lock_with_cpp_exporter(Some(&exporter)))
            .unwrap_or_else(|error| panic!("{relative}: {error}"));
        let mut generated = vec![PathBuf::from(click::project::LOCK_NAME)];
        files(prepared, Path::new(".click"), &mut generated);
        for file in generated {
            let bytes = fs::read(prepared.join(&file)).unwrap();
            if refresh {
                fs::create_dir_all(committed.join(&file).parent().unwrap()).unwrap();
                fs::write(committed.join(&file), &bytes).unwrap();
            }
            assert_eq!(
                bytes,
                fs::read(committed.join(&file)).unwrap(),
                "{relative}/{}: run scripts/refresh-cpp-imports.sh",
                file.display()
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: exceptional memory proof expansion and replay"]
fn scalar_exception_returns_changed_memory_and_borrowed_authority() {
    let project = Project::with_fixture(
        "caller.cpp",
        "caller",
        r#"
void update(int* value, bool fail) {
    if (fail) { *value = 9; throw 7; }
    *value = 7;
}
void caller(int* value, bool fail) { update(value, fail); }
"#,
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("caller", "caller.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let prepared = load_import(&project.config()).unwrap();
    let source = r#"verifying "caller.cpp";
void update(int32* value, bool fail) throws int32 {
    owns value[0];
    ensures value[0] == 7;
    exceptional ensures value[0] == 9;
    exceptional ensures exception == 7;
}
void caller(int32* value, bool fail) throws int32 {
    owns value[0];
    ensures value[0] == 7;
    exceptional ensures value[0] == 9;
    exceptional ensures exception == 7;
}
"#;
    check_return_call_sidecar(&project, &prepared, source);
    let sidecar = project.directory.join("false.click");
    for false_source in [
        source.replace(
            "exceptional ensures value[0] == 9;",
            "exceptional ensures value[0] == old(value[0]);",
        ),
        source.replacen("    owns value[0];", "    views value[0];", 1),
    ] {
        fs::write(&sidecar, &false_source).unwrap();
        let parsed = read_click_project(&sidecar, &false_source).unwrap();
        verify_program_prepared_project(&parsed, &prepared).expect_err(
            "a false exceptional state or read-only authority cannot certify the write",
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: borrowed authority cannot be consumed on a throwing exit"]
fn scalar_exception_refuses_lost_borrowed_authority() {
    let project = Project::with_fixture(
        "abandon.cpp",
        "abandon",
        "void take(int* value) noexcept;\nvoid abandon(int* value) { take(value); throw 7; }\n",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("abandon", "abandon.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let prepared = load_import(&project.config()).unwrap();
    let source = r#"verifying "abandon.cpp";
extern void take(int32* value) {
    consumes value[0];
    ensures true;
}
void abandon(int32* value) throws int32 {
    owns value[0];
    ensures true;
    exceptional ensures exception == 7;
}
"#;
    let sidecar = project.directory.join("abandon.click");
    fs::write(&sidecar, source).unwrap();
    let parsed = read_click_project(&sidecar, source).unwrap();
    let error = verify_program_prepared_project(&parsed, &prepared)
        .expect_err("a throwing function must return the authority it borrowed");
    assert!(
        error.message().contains("resource") || error.message().contains("ownership"),
        "{}",
        error.report()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: user-defined opaque exception construction and replay"]
fn typed_aggregate_exceptions_check_initializers_and_return_memory() {
    let project = Project::with_fixture(
        "errors.cpp",
        "relay",
        r#"
namespace errors { struct ParseError { int code; }; }
struct Other { int code; };
void raise(int* counter, int code, bool fail) {
    if (fail) { *counter = code; throw errors::ParseError{code + 1}; }
    *counter = 0;
}
void relay(int* counter, int code, bool fail, Other* marker) {
    raise(counter, code, fail);
}
"#,
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "errors.cpp", true, "typed");
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let prepared = load_import(&project.config()).unwrap();
    let source = r#"verifying "errors.cpp";
void raise(int32* counter, int32 code, bool fail) throws errors::ParseError {
    requires code < 2147483647;
    owns counter[0];
    ensures counter[0] == 0;
    exceptional ensures counter[0] == code;
}
void relay(int32* counter, int32 code, bool fail, struct Other* marker) throws errors::ParseError {
    requires code < 2147483647;
    owns counter[0];
    ensures counter[0] == 0;
    exceptional ensures counter[0] == code;
}
"#;
    check_return_call_sidecar(&project, &prepared, source);
    let sidecar_path = project.directory.join("arithmetic.click");
    let parsed = read_click_project(&sidecar_path, source).unwrap();
    let mut rewritten = parsed.clone();
    for label in ["raise.contract", "relay.contract"] {
        let expanded = expand_project_claim_source_by_label(
            &rewritten,
            &ProgramInputs::program(&prepared),
            label,
        )
        .unwrap();
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&rewritten, &prepared)
                .unwrap();
        rewritten = parsed.with_entry_source(expanded.clone());
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&prepared),
            label,
            0,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
    }
    click::surface::without_implicit_solve(|| {
        verify_program_prepared_project(&rewritten, &prepared)
    })
    .unwrap();
    let sidecar = project.directory.join("bad.click");
    for (name, bad) in [
        (
            "different nominal type",
            source.replace("throws errors::ParseError", "throws Other"),
        ),
        (
            "unresolved type",
            source.replace("throws errors::ParseError", "throws Missing"),
        ),
        (
            "initializer overflow",
            source.replace("    requires code < 2147483647;\n", ""),
        ),
        (
            "lost mutable authority",
            source.replace("owns counter[0];", "views counter[0];"),
        ),
        (
            "false exceptional memory",
            source.replace(
                "exceptional ensures counter[0] == code;",
                "exceptional ensures counter[0] == 0;",
            ),
        ),
        (
            "opaque payload fields",
            source.replace(
                "exceptional ensures counter[0] == code;",
                "exceptional ensures exception.code == code + 1;",
            ),
        ),
    ] {
        fs::write(&sidecar, &bad).unwrap();
        let accepted = read_click_project(&sidecar, &bad)
            .ok()
            .is_some_and(|parsed| verify_program_prepared_project(&parsed, &prepared).is_ok());
        assert!(!accepted, "accepted {name}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: empty user exception tags and initializer read authority"]
fn typed_empty_exception_tags_and_checked_payload_reads() {
    for (file, selected, cpp, source) in [
        (
            "tag.cpp",
            "marker",
            "namespace errors { struct End {}; } void marker(bool fail) { if (fail) { throw errors::End{}; } }",
            r#"verifying "tag.cpp";
void marker(bool fail) throws errors::End { ensures true; exceptional ensures true; }
"#,
        ),
        (
            "pointer-read.cpp",
            "from_memory",
            "struct ReadError { int code; }; void from_memory(const int* p) { throw ReadError{p[0]}; }",
            r#"verifying "pointer-read.cpp";
void from_memory(const int32* p) throws ReadError { views p[0]; ensures true; exceptional ensures true; }
"#,
        ),
        (
            "read.cpp",
            "from_reference",
            "struct ReadError { int code; }; void from_reference(const int& value) { throw ReadError{value}; }",
            r#"verifying "read.cpp";
void from_reference(const int32& value) throws ReadError { views value; ensures true; exceptional ensures true; }
"#,
        ),
    ] {
        let project = Project::with_fixture(file, selected, cpp);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(selected, file, true, "typed");
        refresh_import(&project.config()).unwrap();
        let prepared = load_import(&project.config()).unwrap();
        check_return_call_sidecar(&project, &prepared, source);
        if selected == "from_reference" || selected == "from_memory" {
            let bad = source
                .replace("views value;", "")
                .replace("views p[0];", "");
            let sidecar = project.directory.join("bad.click");
            fs::write(&sidecar, &bad).unwrap();
            let parsed = read_click_project(&sidecar, &bad).unwrap();
            verify_program_prepared_project(&parsed, &prepared)
                .expect_err("opaque construction must still read its initializer with authority");
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: user exception source and artifact admission controls"]
fn typed_exceptions_refuse_unmodeled_construction_and_corrupt_fields() {
    for cpp in [
        "struct Error { int code; explicit Error(int n) noexcept : code(n) {} }; void probe() { throw Error{1}; }",
        "struct Error { int code; ~Error() noexcept {} }; void probe() { throw Error{1}; }",
        "struct Error { int code; }; void probe(Error& e) { throw e; }",
        "struct Error { int code; }; void probe() { throw Error{}; }",
    ] {
        let project = Project::with_fixture("refused.cpp", "probe", cpp);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior("probe", "refused.cpp", true, "typed");
        assert!(refresh_import(&project.config()).is_err(), "admitted {cpp}");
    }
    let project = Project::with_fixture(
        "error.cpp",
        "probe",
        "struct Error { int code; }; void probe() { throw Error{1}; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("probe", "error.cpp", true, "typed");
    refresh_import(&project.config()).unwrap();
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut artifact = original.clone();
        let statement = &mut artifact["functions"][0]["body"][0];
        match mutation {
            0 => statement["fields"] = serde_json::json!([]),
            1 => statement["fields"][0]["field"]["record_declaration_id"] = "wrong".into(),
            2 => statement["value_type"]["name"] = "Missing".into(),
            3 => artifact["exception_behavior"] = "scalar_int32".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
        let mut locked = lock.clone();
        use sha2::{Digest, Sha256};
        lock_source_mut(&mut locked)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut locked)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec_pretty(&locked).unwrap()).unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "accepted artifact mutation {mutation}"
        );
    }
}

fn check_native_const_pointer_composition(native: &str, proof: &str) {
    let cpp = format!(
        r#"
{native} read(const {native}* p) noexcept {{ return p[0]; }}
{native}* identity({native}* p) noexcept {{ return p; }}
const {native}* freeze({native}* p) noexcept {{ return identity(p); }}
const {native}* choose({native}* p) noexcept {{
    const {native}* q = static_cast<const {native}*>(p);
    q = freeze(p);
    return q;
}}
{native} probe({native}* p) noexcept {{
    const {native}* q = choose(p);
    return read(q);
}}
"#
    );
    let project = Project::with_fixture("const.cpp", "probe", &cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = format!(
        r#"verifying "const.cpp";
{proof} read(const {proof}* p) {{ views p[0]; ensures result == p[0]; }}
{proof}* identity({proof}* p) {{ ensures result == p; }}
const {proof}* freeze({proof}* p) {{ ensures result == p; }}
const {proof}* choose({proof}* p) {{ ensures result == p; }}
{proof} probe({proof}* p) {{ views p[0]; ensures result == p[0]; }}
"#
    );
    check_return_call_sidecar(&project, &import, &source);
    let path = project.directory.join("arithmetic.click");
    let parsed = read_click_project(&path, &source).unwrap();
    let labels = project_smart_tactic_source_sites(&parsed, &ProgramInputs::program(&import))
        .unwrap()
        .into_iter()
        .map(|site| site.claim_label)
        .collect::<std::collections::BTreeSet<_>>();
    let mut rewritten = parsed.clone();
    for label in labels {
        let expanded = expand_project_claim_source_by_label(
            &rewritten,
            &ProgramInputs::program(&import),
            &label,
        )
        .unwrap();
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&rewritten, &import).unwrap();
        rewritten = parsed.with_entry_source(expanded.clone());
        let position =
            project_tactic_source_position(&rewritten, &ProgramInputs::program(&import), &label, 0)
                .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
    }
    click::surface::without_implicit_solve(|| verify_program_prepared_project(&rewritten, &import))
        .unwrap();
    for bad in [
        source.replace("views p[0];", ""),
        source.replace(
            &format!("read(const {proof}* p)"),
            &format!("read({proof}* p)"),
        ),
        source.replace(
            &format!("const {proof}* choose"),
            &format!("{proof}* choose"),
        ),
        source.replace("ensures result == p[0];", "ensures result != p[0];"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let accepted = read_click_project(&path, &bad)
            .ok()
            .is_some_and(|parsed| verify_program_prepared_project(&parsed, &import).is_ok());
        assert!(
            !accepted,
            "accepted weakened const signature, missing authority or false value: {bad}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: const int pointer composition, full expansion and retained replay"]
fn cpp_const_pointer_int_composition() {
    check_native_const_pointer_composition("int", "int32");
}
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: const unsigned pointer composition, full expansion and retained replay"]
fn cpp_const_pointer_unsigned_composition() {
    check_native_const_pointer_composition("unsigned int", "uint32");
}
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: const byte pointer composition, full expansion and retained replay"]
fn cpp_const_pointer_byte_composition() {
    check_native_const_pointer_composition("unsigned char", "uint8");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: const-qualified callback parameters and results"]
fn cpp_const_pointer_callbacks_preserve_qualified_signatures() {
    let project = Project::with_fixture(
        "callback.cpp",
        "probe",
        r#"
const int* identity(const int* p) noexcept { return p; }
const int* invoke(const int* (*f)(const int*) noexcept, const int* p) noexcept {
    const int* (*g)(const int*) noexcept = f;
    return g(p);
}
const int* probe(const int* p) noexcept { return invoke(&identity, p); }
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "callback.cpp";
contract const int32* Identity(const int32* p) { ensures result == p; }
const int32* identity(const int32* p) { ensures result == p; }
theorem identity_refines() { ensures Identity(&identity) by { unfold(Identity(&identity)); close(); } }
const int32* invoke(const int32* (*f)(const int32*), const int32* p) {
    requires Identity(f); ensures result == p;
}
const int32* probe(const int32* p) { ensures result == p; } by { apply(identity_refines()); step_until(function.exit); close(); }
"#;
    check_return_call_sidecar(&project, &import, source);
    for bad in [
        source.replace("(*f)(const int32*)", "(*f)(int32*)"),
        source.replace("const int32* (*f)", "int32* (*f)"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let accepted = read_click_project(&path, &bad)
            .ok()
            .is_some_and(|parsed| verify_program_prepared_project(&parsed, &import).is_ok());
        assert!(!accepted, "callback signature lost const");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: native const pointer views do not freeze mutable aliases"]
fn cpp_const_pointer_alias_reads_after_mutable_store_and_null_returns() {
    // The original direct const-pointer read, previously an admission refusal.
    let direct = Project::with_fixture(
        "increment.cpp",
        "increment",
        "int increment(const int* value) noexcept {\n    return *value;\n}\n",
    );
    refresh_import(&direct.config()).unwrap();
    let imported = load_import(&direct.config()).unwrap();
    check_return_call_sidecar(
        &direct,
        &imported,
        "verifying \"increment.cpp\"; int32 increment(const int32* value) { views value[0]; ensures result == value[0]; }",
    );
    let project = Project::with_fixture(
        "alias.cpp",
        "probe",
        "int probe(int* p) noexcept { const int* q = p; *p = 7; return q[0]; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"alias.cpp\"; int32 probe(int32* p) { owns p[0]; ensures p[0] == 7; ensures result == 7; }",
    );
    for expression in ["nullptr", "0", "static_cast<const int*>(nullptr)"] {
        let cpp = format!("const int* probe() noexcept {{ return {expression}; }}");
        let project = Project::with_fixture("null.cpp", "probe", &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        check_return_call_sidecar(
            &project,
            &import,
            "verifying \"null.cpp\"; const int32* probe() { ensures result == 0; }",
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: const pointer source and artifact controls"]
fn cpp_const_pointer_refuses_removal_stores_and_forged_qualification() {
    for cpp in [
        "int probe(const int* p) noexcept { *p = 1; return *p; }",
        "int probe(const int* p) noexcept { int* q = const_cast<int*>(p); return *q; }",
        "int probe(const volatile int* p) noexcept { return *p; }",
        "unsigned char probe(const char* p) noexcept { return *p; }",
    ] {
        let project = Project::with_fixture("refused.cpp", "probe", cpp);
        assert!(refresh_import(&project.config()).is_err(), "admitted {cpp}");
    }
    use sha2::{Digest, Sha256};
    let rewrite = |project: &Project, artifact: serde_json::Value, lock: &serde_json::Value| {
        let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
        let mut lock = lock.clone();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    };
    let project = Project::with_fixture(
        "qualify.cpp",
        "probe",
        "int probe(int* p) noexcept { const int* q = p; return *q; }",
    );
    refresh_import(&project.config()).unwrap();
    let original: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..3 {
        let mut artifact = original.clone();
        let cast = &mut artifact["functions"][0]["body"][0]["initializer"]["value"];
        assert_eq!(cast["kind"], "pointer_qualification");
        match mutation {
            0 => cast["value_type"]["pointee"]["is_const"] = false.into(),
            1 => cast["value_type"]["pointee"]["signed"] = false.into(),
            2 => cast["value"]["value_type"]["pointee"]["is_const"] = true.into(),
            _ => unreachable!(),
        }
        rewrite(&project, artifact, &lock);
        assert!(
            load_import(&project.config()).is_err(),
            "accepted qualification mutation {mutation}"
        );
    }
    let project = Project::with_fixture(
        "store.cpp",
        "probe",
        "int probe(const int* p) noexcept { return *p; }",
    );
    refresh_import(&project.config()).unwrap();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    let returned = artifact["functions"][0]["body"][0].clone();
    let mut value_type = returned["value"]["value_type"].clone();
    value_type["is_const"] = false.into();
    let store = serde_json::json!({"kind":"store", "pointer":returned["value"]["pointer"], "value":{"kind":"integer_literal", "value":"1", "value_type":value_type, "span":returned["span"]}, "span":returned["span"]});
    artifact["functions"][0]["body"] = serde_json::json!([store, returned]);
    rewrite(&project, artifact, &lock);
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("store pointer"), "{error}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: const pointer constructor and getter composition"]
fn cpp_const_pointer_constructed_view_getter_composes() {
    let project = Project::with_fixture(
        "view.cpp",
        "probe",
        r#"
struct View {
    const int* data;
    explicit View(const int* p) noexcept : data(p) {}
    int get() const noexcept { return *data; }
};
int probe(const int* p) noexcept { View view(p); return view.get(); }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "view.cpp";
View::View(const int32* p) { owns this->data; ensures this->data == p; }
int32 View::get() const { views this->data; views this->data[0]; ensures result == this->data[0]; }
int32 probe(const int32* p) { views p[0]; ensures result == p[0]; }
"#;
    check_return_call_sidecar(&project, &import, source);
}

fn check_noexcept_replay_all(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    check_return_call_sidecar(project, import, source);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), source).unwrap();
    let labels = project_smart_tactic_source_sites(&parsed, &ProgramInputs::program(import))
        .unwrap()
        .into_iter()
        .map(|site| site.claim_label)
        .collect::<std::collections::BTreeSet<_>>();
    let mut rewritten = parsed.clone();
    for label in labels {
        let expanded = expand_project_claim_source_by_label(
            &rewritten,
            &ProgramInputs::program(import),
            &label,
        )
        .unwrap();
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&rewritten, import).unwrap();
        rewritten = parsed.with_entry_source(expanded.clone());
        let position =
            project_tactic_source_position(&rewritten, &ProgramInputs::program(import), &label, 0)
                .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
    }
    click::surface::without_implicit_solve(|| verify_program_prepared_project(&rewritten, import))
        .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: checked scalar noexcept calls, guarded throws and replay"]
fn cpp_noexcept_scalar_boundaries_require_no_escaping_exception() {
    let project = Project::with_fixture(
        "checked.cpp",
        "probe",
        r#"
int direct(int x, bool fail) noexcept { if (fail) { throw 7; } return x; }
int leaf(int x) noexcept { return x; }
int fallible(int x, bool fail) { if (fail) { throw 7; } return leaf(x); }
int guarded(int x, bool fail) noexcept { return fallible(x, fail); }
int probe(int x, bool fail) { int value = direct(x, fail); return guarded(value, fail); }
"#,
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("probe", "checked.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "checked.cpp";
int32 direct(int32 x, bool fail) { requires fail == false; ensures result == x; }
int32 leaf(int32 x) { ensures result == x; }
int32 fallible(int32 x, bool fail) throws int32 { ensures result == x; exceptional ensures fail == true; exceptional ensures exception == 7; }
int32 guarded(int32 x, bool fail) { requires fail == false; ensures result == x; }
int32 probe(int32 x, bool fail) { requires fail == false; ensures result == x; }
"#;
    check_noexcept_replay_all(&project, &import, source);
    for bad in [
        source.replace("requires fail == false;", ""),
        source.replace(
            "int32 guarded(int32 x, bool fail) {",
            "int32 guarded(int32 x, bool fail) throws int32 {",
        ),
        source.replace(
            "int32 leaf(int32 x) {",
            "int32 leaf(int32 x) throws int32 {",
        ),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let accepted = read_click_project(&path, &bad)
            .ok()
            .is_some_and(|parsed| verify_program_prepared_project(&parsed, &import).is_ok());
        assert!(
            !accepted,
            "accepted escaping exception or throwing noexcept contract"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: typed noexcept(true/false), guarded opaque exits and replay"]
fn cpp_noexcept_typed_conditions_are_checked_at_the_boundary() {
    let project = Project::with_fixture(
        "typed.cpp",
        "probe",
        r#"
struct Error { int code; };
int leaf(int x) noexcept { return x; }
int fallible(int x, bool fail) { if (fail) { throw Error{x}; } return leaf(x); }
int guarded(int x, bool fail) noexcept(true) { return fallible(x, fail); }
int probe(int x, bool fail) noexcept(false) { return guarded(x, fail); }
"#,
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("probe", "typed.cpp", true, "typed");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(!import.export().functions[0].declared_noexcept);
    assert!(
        import
            .export()
            .reachable_functions
            .iter()
            .find(|function| function.name == "guarded")
            .unwrap()
            .declared_noexcept
    );
    let source = r#"verifying "typed.cpp";
int32 leaf(int32 x) { ensures result == x; }
int32 fallible(int32 x, bool fail) throws Error { ensures result == x; exceptional ensures fail == true; }
int32 guarded(int32 x, bool fail) { requires fail == false; ensures result == x; } by {
    step_until(call(0).entry);
    outcomes {
        returned => { step_until(function.exit); close(); }
        threw => { have fail == true; have false by { contradiction(fail); }; close(); }
    }
}
int32 probe(int32 x, bool fail) throws Error { requires fail == false; ensures result == x; exceptional ensures true; }
"#;
    click::surface::with_proof_trace("guarded", || {
        check_noexcept_replay_all(&project, &import, source)
    });
    for bad in [
        source.replace("requires fail == false;", ""),
        source.replace(
            "int32 guarded(int32 x, bool fail) {",
            "int32 guarded(int32 x, bool fail) throws Error {",
        ),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let accepted = read_click_project(&path, &bad)
            .ok()
            .is_some_and(|parsed| verify_program_prepared_project(&parsed, &import).is_ok());
        assert!(
            !accepted,
            "accepted escaping opaque exception or noexcept(true) weakening"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: noexcept constructors/getters in opaque exception profiles"]
fn cpp_noexcept_constructors_and_getters_compose_with_throwing_profiles() {
    for profile in ["typed", "ios_failure"] {
        let project = Project::with_fixture(
            "view.cpp",
            "probe",
            r#"
struct View {
    int value;
    explicit View(int x) noexcept : value(x) {}
    int get() const noexcept { return value; }
};
int probe(int x) { View view(x); return view.get(); }
"#,
        );
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior("probe", "view.cpp", true, profile);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = r#"verifying "view.cpp";
View::View(int32 x) { owns this->value; ensures this->value == x; }
int32 View::get() const { views this->value; ensures result == this->value; }
int32 probe(int32 x) { ensures result == x; }
"#;
        check_noexcept_replay_all(&project, &import, source);
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: unconditional noexcept throws must fail verification"]
fn cpp_noexcept_does_not_trust_the_source_promise() {
    for (profile, cpp, payload) in [
        (
            "scalar_int32",
            "void probe() noexcept { throw 7; }",
            "int32",
        ),
        (
            "typed",
            "struct Error {}; void probe() noexcept { throw Error{}; }",
            "Error",
        ),
    ] {
        let project = Project::with_fixture("escape.cpp", "probe", cpp);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior("probe", "escape.cpp", true, profile);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        for signature in [
            "void probe()".to_string(),
            format!("void probe() throws {payload}"),
        ] {
            let source = format!("verifying \"escape.cpp\"; {signature} {{ ensures true; }}");
            let path = project.directory.join("escape.click");
            fs::write(&path, &source).unwrap();
            let parsed = read_click_project(&path, &source).unwrap();
            assert!(
                verify_program_prepared_project(&parsed, &import).is_err(),
                "trusted noexcept promise or exposed its exception"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: noexcept catches internal scalar exceptions"]
fn cpp_noexcept_scalar_catches_can_finish_normally() {
    // Retain both frontiers: a throw at the end of the try body and a
    // throw that abandons a remaining statement before entering the handler.
    for (tail, normal) in [("", 3), ("result = 4;", 4)] {
        let cpp = format!(
            r#"
int probe(bool fail) noexcept {{
    int result = 3;
    try {{ if (fail) {{ throw 7; }} {tail} }} catch (int error) {{ result = error; }}
    return result;
}}
"#
        );
        let project = Project::with_fixture("caught.cpp", "probe", &cpp);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior("probe", "caught.cpp", true, "scalar_int32");
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            r#"verifying "caught.cpp";
int32 probe(bool fail) {{ ensures fail == false or result == 7; ensures fail == true or result == {normal}; }} by {{
    if fail {{ step_until(function.exit); close(); }} else {{ step_until(function.exit); close(); }}
}}
"#
        );
        click::surface::with_proof_trace("probe", || {
            check_noexcept_replay_all(&project, &import, &source)
        });
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: noexcept scalar cleanup, body proof and replay"]
fn cpp_noexcept_scalar_cleanup_remains_checked_on_normal_paths() {
    check_noexcept_cleanup("scalar_int32", "", "7");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: noexcept typed cleanup, body proof, replay and unwind refusals"]
fn cpp_noexcept_typed_cleanup_remains_checked_on_normal_paths() {
    check_noexcept_cleanup("typed", "struct Error {};", "Error{}");
}

fn check_noexcept_cleanup(profile: &str, declaration: &str, thrown: &str) {
    let cpp = format!(
        r#"
    {declaration}
    struct Guard {{
        int* slot;
        explicit Guard(int* p) noexcept : slot(p) {{}}
        ~Guard() noexcept {{ *slot = 9; }}
    }};
    int fallible(bool fail) {{ if (fail) {{ throw {thrown}; }} return 4; }}
    int probe(int* slot, bool fail) noexcept {{ Guard guard(slot); int result = fallible(fail); return result; }}
    "#
    );
    let project = Project::with_fixture("cleanup.cpp", "probe", &cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("probe", "cleanup.cpp", true, profile);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "cleanup.cpp";
    Guard::Guard(int32* p) { owns this->slot; owns p[0]; ensures this->slot == p; ensures separate(memory(*this), memory(this->slot[0..1])); }
    Guard::~Guard() { requires separate(memory(*this), memory(this->slot[0..1])); views this->slot; owns this->slot[0]; ensures this->slot[0] == 9; }
    int32 fallible(bool fail) { requires fail == false; ensures result == 4; }
    int32 probe(int32* slot, bool fail) { requires fail == false; owns slot[0]; ensures slot[0] == 9; ensures result == 4; }
    "#.to_string();
    click::surface::with_proof_trace("probe", || {
        check_noexcept_replay_all(&project, &import, &source)
    });
    for bad in [
        source.replace("requires fail == false;", ""),
        source.replace("ensures slot[0] == 9;", "ensures slot[0] == old(slot[0]);"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
    if profile == "typed" {
        for replacement in [
            "int probe(int* slot, bool fail) { Guard guard(slot); int result = fallible(fail); return result; }",
            "int probe(int* slot, bool fail) { { Guard guard(slot); fallible(fail); } return 4; }",
        ] {
            let changed = cpp.replace("int probe(int* slot, bool fail) noexcept { Guard guard(slot); int result = fallible(fail); return result; }", replacement);
            let refused = Project::with_fixture("unwind.cpp", "probe", &changed);
            refused.write_exception_enabled_compilation_database();
            refused.write_config_with_exception_behavior("probe", "unwind.cpp", true, "typed");
            let error = refresh_import(&refused.config()).unwrap_err();
            assert!(
                error.contains("class unwinding remains unsupported"),
                "{error}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: record reference local field spelling and complete replay"]
fn cpp_record_reference_locals_name_fields_and_addresses() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int padding; int value; int get() const noexcept { return value; } };
int probe(const Widget& widget) noexcept { const auto& ref = widget; return ref.get(); }
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
int32 Widget::get() const { views this->value; ensures result == this->value; }
int32 probe(const Widget& widget) { views widget.value; ensures result == widget.value; } by {
    step(); step();
    have &ref == &widget;
    have ref.value == widget.value;
}
"#;
    click::surface::with_proof_trace("probe", || {
        check_noexcept_replay_all(&project, &import, source)
    });
    for bad in [
        source.replace("views widget.value;", ""),
        source.replace(
            "ensures result == widget.value;",
            "ensures result == widget.value + 1;",
        ),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: mutable record reference aliases and const observations"]
fn cpp_record_reference_locals_keep_aliases_and_mutation_authority() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int padding; int value; };
int probe(Widget& widget, int value) noexcept {
    auto& ref = widget;
    auto& other = ref;
    const Widget& observed = other;
    other.value = value;
    return observed.value;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
int32 probe(Widget& widget, int32 value) {
    owns widget.value;
    views widget.padding;
    ensures result == value;
    ensures widget.value == value;
    ensures widget.padding == old(widget.padding);
} by {
    step(); step(); step(); step(); step(); step();
    have &ref == &widget;
    have &other == &widget;
    have &observed == &widget;
}
"#;
    click::surface::with_proof_trace("probe", || {
        check_noexcept_replay_all(&project, &import, source)
    });
    for bad in [
        source.replace("owns widget.value;", "views widget.value;"),
        source.replace("owns widget.value;", ""),
        source.replace("ensures result == value;", "ensures result == 0;"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: references to local record storage and nested record subobjects"]
fn cpp_record_reference_locals_bind_objects_and_nested_members() {
    for (cpp, source) in [
        (
            r#"struct Widget { int padding; int value; };
int probe() noexcept { Widget widget{3, 7}; auto& ref = widget; ref.value = 9; return widget.value; }
"#,
            r#"verifying "reference.cpp";
int32 probe() { ensures result == 9; }
"#,
        ),
        (
            r#"struct Widget { int padding; int value; }; struct Outer { int first; Widget child; };
int probe(Outer& outer, int value) noexcept { auto& ref = outer.child; ref.value = value; return outer.child.value; }
"#,
            r#"verifying "reference.cpp";
int32 probe(Outer& outer, int32 value) { owns outer.child.value; ensures outer.child.value == value; ensures result == value; }
"#,
        ),
    ] {
        let project = Project::with_fixture("reference.cpp", "probe", cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        click::surface::with_proof_trace("probe", || {
            check_noexcept_replay_all(&project, &import, source)
        });
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: record pointer reference binding and invalid-storage rejection"]
fn cpp_record_reference_locals_check_pointer_backing() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int padding; int value; };
int probe(Widget* pointer) noexcept { auto& ref = *pointer; return ref.value; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
int32 probe(Widget* pointer) { views pointer->padding; views pointer->value; ensures result == pointer->value; }
"#;
    click::surface::with_proof_trace("probe", || {
        check_noexcept_replay_all(&project, &import, source)
    });
    let bad = Project::with_fixture(
        "null.cpp",
        "probe",
        "struct Widget { int value; }; int probe() noexcept { Widget* pointer = nullptr; auto& ref = *pointer; return 0; }",
    );
    refresh_import(&bad.config()).unwrap();
    let import = load_import(&bad.config()).unwrap();
    let source = "verifying \"null.cpp\"; int32 probe() { ensures result == 0; }";
    fs::write(bad.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&bad.directory.join("bad.click"), source).unwrap();
    assert!(
        verify_program_prepared_project(&parsed, &import).is_err(),
        "binding a null record reference must fail without any field read"
    );
}

#[test]
fn cpp_record_reference_locals_refuse_forged_nominal_types_and_const() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int value; }; struct Other { int value; };
int probe(const Widget& widget, const Other& other) noexcept { const Widget& ref = widget; return 0; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let original_artifact = fs::read(project.artifact()).unwrap();
    let original_lock = fs::read(project.lock()).unwrap();
    for mutation in 0..3 {
        let mut artifact: serde_json::Value = serde_json::from_slice(&original_artifact).unwrap();
        let other = artifact["records"]
            .as_array()
            .unwrap()
            .iter()
            .find(|record| record["name"] == "Other")
            .unwrap()
            .clone();
        let declaration = &mut artifact["functions"][0]["body"][0];
        if mutation == 2 {
            declaration["initializer"] = serde_json::json!({"kind":"uninitialized"});
        } else {
            for target in ["local", "initializer"] {
                let ty = if target == "local" {
                    &mut declaration["local"]["value_type"]["pointee"]
                } else {
                    &mut declaration["initializer"]["value"]["value_type"]["pointee"]
                };
                if mutation == 0 {
                    ty["is_const"] = false.into();
                } else {
                    ty["declaration_id"] = other["declaration_id"].clone();
                    ty["name"] = other["name"].clone();
                }
            }
        }
        let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
        let mut lock: serde_json::Value = serde_json::from_slice(&original_lock).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(
            error.contains("reference binding") || error.contains("local initializer"),
            "{error}"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: aliases grant no memory authority and never resurrect retired record storage"]
fn cpp_record_reference_locals_keep_storage_lifetimes_separate() {
    let alias = Project::with_fixture(
        "alias.cpp",
        "probe",
        "struct Widget { int value; }; int probe(Widget& widget) noexcept { Widget& ref = widget; return 0; }",
    );
    refresh_import(&alias.config()).unwrap();
    let import = load_import(&alias.config()).unwrap();
    check_noexcept_replay_all(
        &alias,
        &import,
        "verifying \"alias.cpp\"; int32 probe(Widget& widget) { ensures result == 0; }",
    );
    let project = Project::with_fixture(
        "lifetime.cpp",
        "probe",
        r#"
struct Widget {
    int value;
    explicit Widget(int v) noexcept : value(v) {}
    ~Widget() noexcept { value = 0; }
};
int probe() noexcept {
    Widget* pointer = nullptr;
    { Widget widget(7); pointer = &widget; }
    auto& ref = *pointer;
    return 0;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "lifetime.cpp";
Widget::Widget(int32 v) { owns this->value; ensures this->value == v; }
Widget::~Widget() { owns this->value; ensures this->value == 0; }
int32 probe() { ensures result == 0; }
"#;
    let path = project.directory.join("lifetime.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    assert!(
        verify_program_prepared_project(&parsed, &import).is_err(),
        "an unused reference must still reject retired record storage"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: returned member write with sibling view and complete replay"]
fn cpp_returned_member_pointer_write_retains_its_source_domain() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int value; };
struct Outer { int first; Widget child; };
int* child(Outer& outer) noexcept { return &outer.child.value; }
int probe(Outer& outer, int value) noexcept { auto* ref = child(outer); *ref = value; return outer.child.value; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
int32* child(Outer& outer) { views outer.first; views outer.child.value; ensures result == &outer.child.value; }
int32 probe(Outer& outer, int32 value) { owns outer.child.value; views outer.first; ensures result == value; ensures outer.child.value == value; ensures outer.first == old(outer.first); } by {
    step(); step(); step();
    have ref == &outer.child.value by { close(); }
    have separate(memory(outer.child.value), memory(outer.first)) by { close(); }
    have separate(memory(ref[0]), memory(outer.first)) by {
        rewrite(ref, &outer.child.value); close();
    }
    step();
}
"#;
    let path = project.directory.join("arithmetic.click");
    fs::write(&path, source).unwrap();
    let mut parsed = read_click_project(&path, source).unwrap();
    for (label, target) in [
        ("child.ensures_0", "ensures result == &outer.child.value"),
        ("probe.contract", "ensures result == value"),
    ] {
        let expanded =
            expand_project_claim_source_by_label(&parsed, &ProgramInputs::program(&import), label)
                .unwrap_or_else(|error| panic!("{}", error.report()));
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, &import)
                .unwrap_or_else(|error| panic!("{}", error.report()));
        let offset = expanded.find(target).unwrap();
        let prefix = &expanded[..offset];
        let line = prefix.bytes().filter(|b| *b == b'\n').count() + 1;
        let column = prefix.rsplit('\n').next().unwrap().chars().count() + 1;
        session
            .verify_at_project(&expanded, line, column)
            .unwrap_or_else(|error| panic!("{}", error.report()));
        drop(session);
        parsed = parsed.with_entry_source(expanded);
    }
    click::surface::without_implicit_solve(|| verify_program_prepared_project(&parsed, &import))
        .unwrap_or_else(|error| panic!("{}", error.report()));
    for bad in [
        source.replace("owns outer.child.value;", "views outer.child.value;"),
        source.replace(
            "ensures result == &outer.child.value;",
            "ensures (result as uint64) == (&outer.child.value as uint64);",
        ),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: record reference result identity, mutation, and full replay"]
fn cpp_record_reference_results_preserve_aliases_and_mutation() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int padding; int value; };
Widget& identity(Widget& widget) noexcept { Widget& alias = widget; return alias; }
Widget& relay(Widget& widget) noexcept { return identity(widget); }
Widget& probe(Widget& widget) noexcept { auto& ref = relay(widget); ref.value = 7; return ref; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
Widget& identity(Widget& widget) { ensures &result == &widget; }
Widget& relay(Widget& widget) { ensures &result == &widget; }
Widget& probe(Widget& widget) {
    owns widget.value; views widget.padding;
    ensures &result == &widget;
    ensures result.value == 7;
    ensures widget.value == 7;
    ensures widget.padding == old(widget.padding);
}
"#;
    click::surface::with_proof_trace("probe", || {
        check_noexcept_replay_all(&project, &import, source)
    });
    for bad in [
        source.replace("owns widget.value;", "views widget.value;"),
        source.replace("owns widget.value;", ""),
        source.replace("ensures result.value == 7;", "ensures result.value == 8;"),
        source.replace("Widget& identity", "int32& identity"),
        source.replace("Widget& identity", "Widget* identity"),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: const record result fields and local call bindings"]
fn cpp_record_reference_results_keep_const_fields_and_identity() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
class Widget { public: int padding; int value; };
const Widget& identity(const Widget& widget) noexcept { return widget; }
int probe(const Widget& widget) noexcept { const auto& ref = identity(widget); return ref.value; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
const Widget& identity(const Widget& widget) { views widget.value; ensures &result == &widget; ensures result.value == widget.value; }
int32 probe(const Widget& widget) { views widget.value; ensures result == widget.value; }
"#;
    check_noexcept_replay_all(&project, &import, source);
    for bad in [
        source.replace("views widget.value;", ""),
        source.replace("const Widget& identity", "Widget& identity"),
        source.replace(
            "ensures result == widget.value;",
            "ensures result == widget.value + 1;",
        ),
    ] {
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: record reference result subobject identity and member authority"]
fn cpp_record_reference_results_keep_nested_subobjects() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/cpp-verification/record-reference-results");
    let cpp = fs::read_to_string(fixture.join("reference.cpp")).unwrap();
    let project = Project::with_fixture("reference.cpp", "probe", &cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = fs::read_to_string(fixture.join("reference.click")).unwrap();
    click::surface::with_proof_trace("probe", || {
        check_record_reference_claim_replay(
            &project,
            &import,
            &source,
            &["Outer::get.ensures_0", "child.ensures_0", "probe.contract"],
        )
    });
    let bad = source
        .replace("owns outer.child.value;", "owns outer.first;")
        .replace("views outer.first;", "views outer.child.value;");
    let path = project.directory.join("bad.click");
    fs::write(&path, &bad).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
            .is_err()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: direct access through a returned record reference and proof replay"]
fn cpp_record_reference_results_read_and_write_direct_fields() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/cpp-verification/record-reference-results");
    let cpp = fs::read_to_string(fixture.join("direct.cpp")).unwrap();
    let project = Project::with_fixture("direct.cpp", "probe", &cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let mut pending = vec![lowered.kernel_function().body()];
    let mut operations = Vec::new();
    while let Some(statement) = pending.pop() {
        match statement {
            ProgramStatement::Seq(body) => pending.extend(body.iter().rev().map(AsRef::as_ref)),
            ProgramStatement::StepValue {
                expression: ProgramExpression::TypedLoad { .. },
                ..
            } => operations.push("read right operand".to_owned()),
            ProgramStatement::CallResult { function_name, .. } => operations.push(
                click::surface::source_display_name(function_name)
                    .unwrap_or_else(|| function_name.clone()),
            ),
            ProgramStatement::TypedStore { .. } => operations.push("store field".to_owned()),
            _ => {}
        }
    }
    assert_eq!(
        operations,
        [
            "read right operand",
            "Outer::get",
            "store field",
            "Outer::peek"
        ]
    );
    let source = fs::read_to_string(fixture.join("direct.click")).unwrap();
    click::surface::with_proof_trace("probe", || {
        check_record_reference_claim_replay(
            &project,
            &import,
            &source,
            &[
                "Outer::get.ensures_0",
                "Outer::peek.ensures_0",
                "probe.contract",
            ],
        )
    });
    let read_only = source.replace("owns outer.child.value;", "views outer.child.value;");
    let path = project.directory.join("bad.click");
    fs::write(&path, &read_only).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &read_only).unwrap(), &import)
            .is_err()
    );

    let const_store = Project::with_fixture(
        "direct.cpp",
        "probe",
        &cpp.replace("outer.get().value =", "outer.peek().value ="),
    );
    assert!(refresh_import(&const_store.config()).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: compound field assignment through returned references and proof replay"]
fn cpp_record_reference_results_compound_field_updates() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/cpp-verification/record-reference-results");
    let cpp = fs::read_to_string(fixture.join("compound.cpp")).unwrap();

    for (function, getter, negative_clause, replacement, expected_error) in [
        (
            "add",
            "active",
            "requires state.delta == 2;",
            "",
            "signed overflow",
        ),
        (
            "subtract",
            "current",
            "owns state.counter.value;",
            "views state.counter.value;",
            "missing resource fact `owns",
        ),
    ] {
        let project = Project::with_fixture("compound.cpp", function, &cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let lowered = lower_import(&import).unwrap();
        let mut pending = vec![lowered.kernel_function().body()];
        let mut calls = Vec::new();
        while let Some(statement) = pending.pop() {
            match statement {
                ProgramStatement::Seq(body) => pending.extend(body.iter().rev().map(AsRef::as_ref)),
                ProgramStatement::CallResult { function_name, .. } => {
                    calls.push(click::surface::source_display_name(function_name).unwrap());
                }
                _ => {}
            }
        }
        assert_eq!(calls, [format!("State::{getter}")]);
        let source =
            fs::read_to_string(fixture.join(format!("compound-{function}.click"))).unwrap();
        let getter_claim = if getter == "active" {
            "State::active.contract"
        } else {
            "State::current.ensures_0"
        };
        let claim = format!("{function}.contract");
        click::surface::with_proof_trace(function, || {
            check_record_reference_claim_replay(&project, &import, &source, &[getter_claim, &claim])
        });

        let bad = source.replace(negative_clause, replacement);
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let error =
            verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
                .expect_err("the weakened contract must be rejected");
        assert!(
            error.report().contains(expected_error),
            "{}",
            error.report()
        );
    }
}

fn check_record_reference_claim_replay(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
    claims: &[&str],
) {
    let path = project.directory.join("arithmetic.click");
    fs::write(&path, source).unwrap();
    let mut parsed = read_click_project(&path, source).unwrap();
    let inputs = ProgramInputs::program(import);
    verify_program_prepared_project(&parsed, import).unwrap_or_else(|error| {
        panic!(
            "{}\n{}",
            error.report(),
            error.trace_context_report().unwrap_or_default()
        )
    });
    // A written body can have an implicit closer but no source smart tactic.
    // Expand the declared claims so that these bodies get checked too.
    for claim in claims {
        let expanded = expand_project_claim_source_by_label(&parsed, &inputs, claim)
            .unwrap_or_else(|error| panic!("{claim}: {}", error.report()));
        let (session, _) =
            ProgramVerificationSession::new_program_prepared_project(&parsed, import)
                .unwrap_or_else(|error| panic!("{claim}: {}", error.report()));
        let rewritten = parsed.with_entry_source(expanded.clone());
        let position = project_tactic_source_position(&rewritten, &inputs, claim, 0).unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap_or_else(|error| panic!("{claim}: {}\n{expanded}", error.report()));
        parsed = rewritten;
    }
    click::surface::without_implicit_solve(|| verify_program_prepared_project(&parsed, import))
        .unwrap_or_else(|error| panic!("{}\n{}", error.report(), parsed.entry_source().unwrap()));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: pointer-backed record results and invalid storage rejection"]
fn cpp_record_reference_results_check_pointer_backing() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int padding; int value; };
Widget& dereference(Widget* pointer) noexcept { return *pointer; }
int probe(Widget* pointer) noexcept { auto& ref = dereference(pointer); return ref.value; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
Widget& dereference(Widget* pointer) { views pointer->padding; views pointer->value; ensures &result == pointer; } by {
    step();
    have &result == pointer by { normalize() using {}; }
}
int32 probe(Widget* pointer) { views pointer->padding; views pointer->value; ensures result == pointer->value; }
"#;
    check_record_reference_claim_replay(
        &project,
        &import,
        source,
        &["dereference.contract", "probe.ensures_0"],
    );
    let bad = source.replace("views pointer->value;", "");
    let path = project.directory.join("bad.click");
    fs::write(&path, &bad).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &bad).unwrap(), &import)
            .is_err()
    );
    let null = Project::with_fixture(
        "null.cpp",
        "probe",
        "struct Widget { int value; }; Widget& probe() noexcept { Widget* pointer = nullptr; return *pointer; }",
    );
    refresh_import(&null.config()).unwrap();
    let import = load_import(&null.config()).unwrap();
    let source = "verifying \"null.cpp\"; Widget& probe() { ensures &result == &result; }";
    let path = null.directory.join("bad.click");
    fs::write(&path, source).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, source).unwrap(), &import)
            .is_err()
    );
}

#[test]
fn cpp_record_reference_results_refuse_forged_call_types() {
    use sha2::{Digest, Sha256};
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int value; }; struct Other { int value; };
const Widget& identity(const Widget& widget) noexcept { return widget; }
int probe(const Widget& widget, const Other& other) noexcept { const Widget& ref = identity(widget); return 0; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let original_artifact = fs::read(project.artifact()).unwrap();
    let original_lock = fs::read(project.lock()).unwrap();
    for mutation in 0..3 {
        let mut artifact: serde_json::Value = serde_json::from_slice(&original_artifact).unwrap();
        let other = artifact["records"]
            .as_array()
            .unwrap()
            .iter()
            .find(|record| record["name"] == "Other")
            .unwrap()
            .clone();
        let local_type = &mut artifact["functions"][0]["body"][0]["local"]["value_type"];
        match mutation {
            0 => local_type["pointee"]["is_const"] = false.into(),
            1 => {
                local_type["pointee"]["declaration_id"] = other["declaration_id"].clone();
                local_type["pointee"]["name"] = other["name"].clone();
            }
            _ => local_type["kind"] = "pointer".into(),
        }
        let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
        let mut lock: serde_json::Value = serde_json::from_slice(&original_lock).unwrap();
        lock_source_mut(&mut lock)["artifact"]["sha256"] =
            format!("{:x}", Sha256::digest(&bytes)).into();
        lock_source_mut(&mut lock)["artifact"]["bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
        assert!(
            load_import(&project.config()).is_err(),
            "forged call capture {mutation} must be refused"
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: returned record aliases grant no authority and preserve backing lifetimes"]
fn cpp_record_reference_results_keep_backing_lifetimes_separate() {
    for (cpp, source) in [
        (
            "struct Widget { int value; }; Widget& identity(Widget& widget) noexcept { return widget; } Widget& probe(Widget& widget) noexcept { auto& ref = identity(widget); return ref; }",
            "verifying \"reference.cpp\"; Widget& identity(Widget& widget) { ensures &result == &widget; } Widget& probe(Widget& widget) { ensures &result == &widget; }",
        ),
        (
            "struct Widget { int value; }; Widget& identity(Widget& widget) noexcept { return widget; } int probe() noexcept { Widget widget{7}; auto& ref = identity(widget); ref.value = 9; return widget.value; }",
            "verifying \"reference.cpp\"; Widget& identity(Widget& widget) { ensures &result == &widget; } int32 probe() { ensures result == 9; }",
        ),
        (
            "struct Widget { unsigned char value; }; struct Outer { Widget child; }; Widget& child(Outer& outer) noexcept { return outer.child; } int probe(Outer& outer) noexcept { auto& ref = child(outer); return ref.value; }",
            "verifying \"reference.cpp\"; Widget& child(Outer& outer) { views outer.child.value; ensures &result == &outer.child; } int32 probe(Outer& outer) { views outer.child.value; ensures to_integer(result) == to_integer(outer.child.value); }",
        ),
    ] {
        let project = Project::with_fixture("reference.cpp", "probe", cpp);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        check_noexcept_replay_all(&project, &import, source);
    }
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        r#"
struct Widget { int value; explicit Widget(int v) noexcept : value(v) {} ~Widget() noexcept { value = 0; } };
Widget& dereference(Widget* pointer) noexcept { return *pointer; }
int probe() noexcept { Widget* pointer = nullptr; { Widget widget(7); pointer = &widget; } auto& ref = dereference(pointer); return ref.value; }
"#,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
Widget::Widget(int32 v) { owns this->value; ensures this->value == v; }
Widget::~Widget() { owns this->value; ensures this->value == 0; }
Widget& dereference(Widget* pointer) { views pointer->value; ensures &result == pointer; }
int32 probe() { ensures result == 0; }
"#;
    let path = project.directory.join("bad.click");
    fs::write(&path, source).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, source).unwrap(), &import)
            .is_err()
    );
}
