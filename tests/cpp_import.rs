use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use click::cli::{CInput, parse_mdtest, read_c_inputs, read_click_project};
use click::kernel::{
    CExpression, CFunctionOutcome, CState, CStatement, CType, CUndefinedBehavior, Proposition,
    PureFactContext, int32, prove_symbolic_c_function_execution,
};
use click::languages::cpp::{
    CppBinaryOperator, CppCallArgument, CppCleanup, CppExceptionBehavior, CppExpression,
    CppFunctionKind, CppInitializer, CppProjection, CppStatement, CppType, load_import,
    lower_import, refresh_import,
};
use click::surface::{
    C0VerificationSession, VerifiedClaim, expand_project_claim_source_by_label,
    expand_project_tactic_source_at, project_smart_tactic_source_sites,
    project_tactic_source_position, verify_program_prepared_project,
};

#[test]
fn native_raw_pointer_input_without_span_refuses_arithmetic_offline() {
    let project = Project::with_fixture(
        "raw.cpp",
        "raw_offset",
        "int raw_offset(int* p) { int* q = p + 1; return 0; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("raw_offset", "raw.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let path = project.directory.join("raw.click");
    let source = "verifying \"raw.cpp\"; int32 raw_offset(int32* p) { ensures result == 0; } by { execute(); simp(); }";
    fs::write(&path, source).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, source).unwrap(), &import)
            .unwrap_err();
    assert!(
        error.message().contains("pointer arithmetic")
            || error.message().contains("invalid memory"),
        "{}",
        error.message()
    );
}

#[test]
fn native_raw_pointer_typed_prefix_checks_arithmetic_offline() {
    let project = Project::with_fixture(
        "raw.cpp",
        "raw_offset",
        "int raw_offset(int* p) { int* q = p + 1; return 0; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("raw_offset", "raw.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"raw.cpp\"; int32 raw_offset(int32* p) { views p[0..2]; ensures result == 0; } by { execute(); simp(); }",
    );
}

#[test]
fn native_raw_pointer_forwarding_preserves_opaque_input_offline() {
    let project = Project::with_fixture(
        "forward.cpp",
        "forward",
        "int* forward(int* p) { return p; }",
    );
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("forward", "forward.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"forward.cpp\"; int32* forward(int32* p) { ensures result == p; } by { execute(); simp(); }",
    );
}

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
    check_arithmetic_sidecar(
        &project,
        &import,
        r#"verifying "readonly_wide.cpp";
int32 seven() { ensures result == 7; } by { execute(); simp(); }
uint64 probe() { ensures result == 7u64; } by { execute(); simp(); }
"#,
    );
}

#[test]
// Const scalar construction and constexpr storage must survive offline importing and alias reads.
fn readonly_scalar_initialization_keeps_cpp_object_identity() {
    check_readonly_scalar_initialization(false);
}

#[test]
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
int32 seven() { ensures result == 7; } by { execute(); simp(); }
int32 read(const int32& value) { views value; ensures result == value; } by { execute(); simp(); }
int32 probe() { ensures result == 11; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    if tools {
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
        let expanded = expand_project_claim_source_by_label(
            &parsed,
            &ProgramInputs::program(&import),
            "probe.contract",
        )
        .unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import).unwrap();
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            "probe.contract",
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
                artifact["function"]["body"][0]["initializer"] =
                    serde_json::json!({"kind":"uninitialized"});
            } else {
                let declaration = &mut artifact["function"]["body"][1];
                let ty = declaration["initializer"]["value"]["value_type"].clone();
                let span = declaration["span"].clone();
                declaration["initializer"]["value"] = serde_json::json!({
                    "kind":"integral_cast", "value_type":ty, "span":span,
                    "value":{"kind":"runtime_constant_evaluation", "value_type":{"kind":"boolean","bits":8,"is_const":false}, "span":span}
                });
            }
            let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
            let mut lock: serde_json::Value = serde_json::from_slice(&original_lock).unwrap();
            lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
            lock["artifact_bytes"] = bytes.len().into();
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
// A by-value descriptor copy owns only its fields, and still aliases its backing allocation.
fn trivial_record_parameter_copy_keeps_caller_fields_and_shared_backing() {
    check_trivial_record_parameter_copy(false);
}

#[test]
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

fn check_trivial_record_parameter_copy(tools: bool) {
    let project = Project::with_fixture(
        "copy.cpp",
        "probe",
        "struct View { int* data; int size; }; int change(View value) noexcept { value.size = 7; *value.data = 9; return value.size; } int probe(View& input) noexcept { int result = change(input); return input.size + result + *input.data; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "copy.cpp";
int32 change(struct View value) {
 owns value.data[0..1];
 ensures result == 7;
 ensures load_int32(old(value.data)) == 9;
} by { execute(); simp(); }
int32 probe(struct View& input) {
 views input.data; views input.size;
 owns input.data[0..1];
 requires input.size <= 2147483631;
 ensures result == old(input.size) + 16;
 ensures input.size == old(input.size);
 ensures input.data == old(input.data);
 ensures input.data[0] == 9;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    if tools {
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
        let expanded = expand_project_claim_source_by_label(
            &parsed,
            &ProgramInputs::program(&import),
            "probe.contract",
        )
        .unwrap();
        verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
            .unwrap();
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            "probe.contract",
            0,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
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
        artifact["function"]["body"][0]["initializer"]["arguments"][0]["kind"],
        "record_copy"
    );
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        let argument = &mut forged["function"]["body"][0]["initializer"]["arguments"][0];
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
        import.export().function.body[0],
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
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
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
            0 => forged["function"]["body"][0]["value_type"]["name"] = "Other".into(),
            1 => forged["function"]["body"][0]["source"]["declaration_id"] = "expired_local".into(),
            2 => forged["function"]["body"][0]["span"]["file"] = "unlocked.cpp".into(),
            3 => {
                let record = artifact["records"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|record| record["name"] == "View")
                    .unwrap();
                let field = &record["fields"][0];
                forged["function"]["body"][0]["source"]["projections"] = serde_json::json!([{
                    "record_declaration_id":record["declaration_id"], "declaration_id":field["declaration_id"], "name":field["name"], "span":field["span"]
                }]);
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
fn projected_trivial_record_return_verifies_without_copying_siblings() {
    let project = Project::with_fixture(
        "copy.cpp",
        "copy",
        "struct Extent { unsigned long size; }; struct View { int* data; Extent extent; }; Extent copy(const View& input) noexcept { return input.extent; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        r#"verifying "copy.cpp";
struct Extent copy(const struct View& input) {
 views input.extent.size;
 ensures result.size == input.extent.size;
 ensures input.extent.size == old(input.extent.size);
} by { execute(); simp(); }
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
void Node_constructor(struct Node* this, int32 input) {
 owns this->value;
 owns this->self;
 ensures this->value == input;
 ensures this->self == &this->value;
} by { execute(); simp(); }
int32 probe(int32 input) {
 ensures result == input;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    for label in ["Node_constructor.contract", "probe.contract"] {
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
    check_arithmetic_sidecar(
        &project,
        &import,
        r#"verifying "address.cpp";
const int32& probe(const struct Node& input) {
 views input.value;
 ensures &result == &input.value;
 ensures result == input.value;
} by { execute(); simp(); }
"#,
    );
    use sha2::{Digest, Sha256};
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    artifact["function"]["body"][0]["value"]["address"]["value_type"]["pointee"]["is_const"] =
        false.into();
    let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
    lock["artifact_bytes"] = bytes.len().into();
    fs::write(project.artifact(), bytes).unwrap();
    fs::write(project.lock(), serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    let error = load_import(&project.config()).unwrap_err();
    assert!(
        error.contains("field address changed type or const qualification"),
        "{error}"
    );
}

#[test]
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
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
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
        import.export().function.body[0],
        CppStatement::TrivialCopy { .. }
    ));
    let source = r#"verifying "copy.cpp";
int32 probe(struct View& target, const struct View& source) {
 owns target.data;
 owns target.extent.size;
 views source.extent.size;
 ensures target.data == old(target.data);
 ensures target.extent.size == source.extent.size;
 ensures source.extent.size == old(source.extent.size);
 ensures result == 0;
} by { execute(); simp(); }
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
                forged["function"]["parameters"][0]["value_type"]["pointee"]["is_const"] =
                    true.into()
            }
            1 => forged["function"]["body"][0]["source"]["projections"] = serde_json::json!([]),
            2 => forged["function"]["body"][0]["span"]["file"] = "unlocked.cpp".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
        self.directory.join("demo.click.import.json")
    }

    fn artifact(&self) -> PathBuf {
        self.directory
            .join(format!("{}.click-cpp.json", self.source_name))
    }

    fn lock(&self) -> PathBuf {
        self.directory.join("demo.click.import.json.lock")
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

    fn write_compilation_database_command_string(&self, command: &str) {
        let database = serde_json::json!([{
            "directory": self.directory,
            "file": self.source_name,
            "command": command,
            "output": "fixture.o"
        }]);
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
        check_arithmetic_sidecar(
            &project,
            &import,
            r#"verifying "once.cpp";
int32 probe(int32& value) {
 owns value;
 ensures value == 7;
 ensures result == 7;
} by { execute(); simp(); }
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
} by { execute(); simp(); }
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
fn expression_observers_preserve_symbolic_field_reads_offline() {
    let project = Project::with_fixture(
        "observe.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; unsigned long probe(const Count& count) noexcept { return count.value + count.size(); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "observe.cpp";
uint64 Count_size(const struct Count* this) {
 views this->value;
 ensures result == this->value;
} by { execute(); simp(); }
uint64 probe(const struct Count& count) {
 views count.value;
 ensures result == count.value + count.value;
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
            "result == count.value + count.value;",
            "result != count.value + count.value;",
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
        let call = &mut forged["function"]["body"][0]["value"]["right"];
        match mutation {
            0 => call["callee"]["declaration_id"] = "missing".into(),
            1 => call["value_type"]["bits"] = 32.into(),
            2 => call["span"]["file"] = "unlocked.cpp".into(),
            3 => forged["reachable_functions"][0]["declared_noexcept"] = false.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
fn expression_observers_normalize_nested_arguments_and_widened_results() {
    let project = Project::with_fixture(
        "observe.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; unsigned long echo(unsigned long value) noexcept { return value; } unsigned long probe(const Count& count) noexcept { return count.value + echo(count.size()); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "observe.cpp";
uint64 Count_size(const struct Count* this) { views this->value; ensures result == this->value; } by { execute(); simp(); }
uint64 echo(uint64 value) { ensures result == value; } by { execute(); simp(); }
uint64 probe(const struct Count& count) { views count.value; ensures result == count.value + count.value; } by { execute(); simp(); }
"#,
    );
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int echo(int value) noexcept { return value; } long relay(int value) noexcept { return echo(value) + 1; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int64 relay(int32 value) { requires value == 0; ensures result == 1i64; } by { execute(); simp(); }
"#,
    );
}

#[test]
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
        let numeric = if condition == "false" { 0 } else { 1 };
        let source = format!(
            r#"verifying "observe.cpp";
bool enabled() {{ ensures result == {numeric}; }} by {{ execute(); simp(); }}
bool read(const struct Count& count) {{ views count.value; requires count.value == 0u64; ensures result == 1; }} by {{ execute(); simp(); }}
bool probe(const struct Count& count) {{ ensures result == result; }} by {{ execute(); simp(); }}
"#
        );
        if condition == "false" {
            check_return_call_sidecar(&project, &import, &source);
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
int32* View_data(const struct View* this) { views this->pointer; ensures result == this->pointer; } by { execute(); simp(); }
int32& probe(const struct View& view) { views view.pointer; views view.pointer[0..1]; ensures &result == view.pointer; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
    let path = project.directory.join("observe.click");
    fs::write(&path, source).unwrap();
    let hostile = source.replace("views view.pointer[0..1];", "");
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
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
uint64 Count_size(struct Count* this) {
 views this->value;
 ensures result == 5u64;
} by { execute(); simp(); }
uint64 probe(struct Count& count) {
 views count.value;
 ensures result == count.value + 5u64;
} by { execute(); simp(); }
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
    let sidecar = "verifying \"macro.cpp\";\nint32 read(int32 value) { ensures result == value; } by { execute(); simp(); }\nint32 probe(int32 value) { ensures result == value; } by { execute(); simp(); }\n";
    check_return_call_sidecar(&project, &import, sidecar);
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
fn reference_result_claim_and_simp_expansion_preserve_address_and_value_spelling() {
    let project = Project::with_fixture(
        "reference.cpp",
        "probe",
        "int& helper(int& value) noexcept { return value; } int& probe(int& value) noexcept { return helper(value); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "reference.cpp";
int32& helper(int32& value) { views value; ensures &result == &value; ensures result == old(value); } by { execute(); simp(); }
int32& probe(int32& value) { views value; ensures &result == &value; ensures result == old(value); } by { execute(); simp(); }
"#;
    let path = project.directory.join("reference.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
    let position = project_tactic_source_position(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
        1,
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
            "verifying \"reference.cpp\";\n{sidecar_type} probe(int32* data) {{ views data[0..1]; ensures &result == data; }} by {{ execute(); simp(); }}\n"
        );
        check_return_call_sidecar(&project, &import, &source);
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
fn runtime_constant_evaluation_keeps_manifest_branch_selection_distinct_offline() {
    for (cpp, expected) in [
        (
            "bool probe() noexcept { return __builtin_is_constant_evaluated(); }",
            0,
        ),
        (
            "constexpr bool evaluated() noexcept { return __builtin_is_constant_evaluated(); } bool probe() noexcept { return evaluated(); }",
            0,
        ),
        (
            "constexpr bool evaluated() noexcept { return __builtin_is_constant_evaluated(); } bool probe() noexcept { if constexpr (evaluated()) { return true; } else { return false; } }",
            1,
        ),
        (
            "bool probe() noexcept { if (__builtin_is_constant_evaluated()) { return true; } else { return false; } }",
            0,
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
            "bool evaluated() { ensures result == 0; } by { execute(); simp(); }\n"
        } else {
            ""
        };
        let source = format!(
            "verifying \"evaluation.cpp\";\n{helper}bool probe() {{ ensures result == {expected}; }} by {{ execute(); simp(); }}\n"
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace(
            &format!("result == {expected}"),
            &format!("result == {}", 1 - expected),
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
            let expression = &mut forged["function"]["body"][0]["value"];
            match mutation {
                0 => expression["value_type"]["bits"] = 64.into(),
                1 => expression["constant_context"] = true.into(),
                2 => expression["span"]["file"] = "unlocked.h".into(),
                _ => unreachable!(),
            }
            let bytes = serde_json::to_vec_pretty(&forged).unwrap();
            let mut forged_lock = lock.clone();
            forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
            forged_lock["artifact_bytes"] = bytes.len().into();
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
    let source = "verifying \"unreachable.cpp\";\nint32 probe(bool enter) { requires enter == 0; ensures result == 0; } by { execute(); simp(); }\n";
    check_return_call_sidecar(&project, &import, source);
    for hostile in [
        source.replace("requires enter == 0;", ""),
        source.replace("enter == 0", "enter == 1"),
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
fn logical_negation_checks_full_width_truth_and_observer_results_offline() {
    for (cpp, helper, parameters, requires) in [
        (
            "bool probe(bool flag) noexcept { return !flag; }",
            "",
            "bool flag",
            "flag == 0",
        ),
        (
            "bool probe(unsigned long value) noexcept { return !value; }",
            "",
            "uint64 value",
            "value == 0u64",
        ),
        (
            "bool ready() noexcept { return false; } bool probe() noexcept { return !ready(); }",
            "bool ready() { ensures result == 0; } by { execute(); simp(); }",
            "",
            "1 == 1",
        ),
        (
            "bool ready() noexcept { return false; } bool probe() noexcept { if (!ready()) { return true; } else { return false; } }",
            "bool ready() { ensures result == 0; } by { execute(); simp(); }",
            "",
            "1 == 1",
        ),
    ] {
        let project = Project::with_fixture("negation.cpp", "probe", cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"negation.cpp\";\n{helper}\nbool probe({parameters}) {{ requires {requires}; ensures result == 1; }} by {{ execute(); simp(); }}\n"
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace("ensures result == 1;", "ensures result == 0;");
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        assert!(
            verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
                .is_err()
        );
        if parameters == "uint64 value" {
            let high = source
                .replace("value == 0u64", "value == 4294967296u64")
                .replace("result == 1", "result == 0");
            check_return_call_sidecar(&project, &import, &high);
        }
    }
}

#[test]
fn clang_export_is_deterministic_typed_and_loads_without_clang() {
    let project = Project::new();
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .args([
            "import",
            "lock",
            project.directory.join("demo.click").to_str().unwrap(),
        ])
        .output()
        .expect("run the ordinary import command");
    assert!(
        output.status.success(),
        "click import failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let reported = String::from_utf8(output.stdout).unwrap();
    assert!(reported.contains(click::languages::cpp::DECLARED_UINT32_BYTE_GUARANTEE));
    assert!(reported.contains("not a C++20 guarantee"));
    let first_artifact = fs::read(project.artifact()).unwrap();
    let first_lock = fs::read(project.lock()).unwrap();
    refresh_import(&project.config()).expect("repeat the same semantic export");
    assert_eq!(fs::read(project.artifact()).unwrap(), first_artifact);
    assert_eq!(fs::read(project.lock()).unwrap(), first_lock);

    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");
    let prepared = load_import(&project.config()).expect("locked loading must not execute Clang");
    assert_eq!(prepared.export().schema, 60);
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
        project.compilation_arguments()
    );
    let function = &prepared.export().function;
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
}

#[test]
fn pinned_uint32_byte_profile_is_reported_and_rejects_rehashed_metadata_offline() {
    use click::languages::cpp::DECLARED_UINT32_BYTE_GUARANTEE;
    use sha2::{Digest, Sha256};

    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(
        import.export().profile.byte_representation_guarantee,
        DECLARED_UINT32_BYTE_GUARANTEE
    );
    let source = "verifying \"increment.cpp\"; int32 increment(int32& value) { owns value; requires value < 2147483647; ensures result == old(value) + 1; ensures value == old(value) + 1; } by { execute(); simp(); }";
    let sidecar = project.directory.join("profile.click");
    fs::write(&sidecar, source).unwrap();
    let verified =
        verify_program_prepared_project(&read_click_project(&sidecar, source).unwrap(), &import)
            .unwrap();
    let selection = verified[0]
        .selection
        .as_ref()
        .expect("checked source selection");
    assert!(selection.runtime_assumptions.iter().any(|assumption| {
        assumption.contains(DECLARED_UINT32_BYTE_GUARANTEE)
            && assumption.contains("not a C++20 guarantee")
    }));

    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for change in 0..13 {
        let mut forged = artifact.clone();
        match change {
            0 => {
                forged["profile"]
                    .as_object_mut()
                    .unwrap()
                    .remove("byte_representation_guarantee");
            }
            1 => {
                forged["profile"]["byte_representation_guarantee"] =
                    "arbitrary_object_bytes_v1".into()
            }
            2 => forged["profile"]["byte_order"] = "big".into(),
            3 => forged["profile"]["pointer_width"] = 32.into(),
            4 => forged["profile"]["long_width"] = 32.into(),
            5 => forged["profile"]["uint32_width"] = 64.into(),
            6 => forged["profile"]["byte_width"] = 16.into(),
            7 => forged["schema"] = 59.into(),
            9 => forged["profile"]["frontend_version"] = "Debian clang version 19.1.70".into(),
            10 => forged["profile"]["frontend_version"] = "unrelated 19.1.7".into(),
            11 => forged["profile"]["frontend_version"] = "clang version 19.1.7git".into(),
            12 => {
                forged["profile"]["frontend_version"] =
                    "clang version 20.0.0 (compatible with 19.1.7)".into()
            }
            _ => {
                forged["profile"]
                    .as_object_mut()
                    .unwrap()
                    .remove("byte_order");
            }
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
        forged_lock["profile"] = forged["profile"].clone();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(
            project.lock(),
            serde_json::to_vec_pretty(&forged_lock).unwrap(),
        )
        .unwrap();
        let error = load_import(&project.config())
            .expect_err(&format!("rehashed unsupported byte profile {change}"));
        let expected_reason = match change {
            0 => "missing field `byte_representation_guarantee`",
            7 => "unsupported C++ exporter schema",
            8 => "missing field `byte_order`",
            _ => "C++ byte representation guarantee must be",
        };
        assert!(
            error.contains(expected_reason),
            "profile mutation {change} must fail its profile check before lock identity: {error}"
        );
    }
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
    assert_eq!(
        prepared.export().profile.compilation_directory,
        build.to_string_lossy()
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
    assert!(
        load_import(&project.config())
            .unwrap_err()
            .contains("preprocessor input inventory differs")
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
fn compilation_database_command_is_selected_locked_and_validated() {
    let project = Project::new();
    refresh_import(&project.config()).expect("export through the selected compilation command");
    let first = load_import(&project.config()).expect("load the locked compilation command");
    let first_identity = first.identity().to_string();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    assert_eq!(
        lock["compilation_database_sha256"].as_str().unwrap().len(),
        64
    );
    assert_eq!(
        lock["profile"]["compilation_command"],
        serde_json::json!(project.compilation_arguments())
    );

    let mut changed = project.compilation_arguments();
    changed.insert(changed.len() - 4, "-DCLICK_COMMAND_VARIANT=1".into());
    project.write_compilation_database_commands(&[changed.clone()]);
    let error = load_import(&project.config()).unwrap_err();
    assert!(error.contains("compilation database differs"), "{error}");
    refresh_import(&project.config()).expect("refresh after an explicit command change");
    let refreshed = load_import(&project.config()).unwrap();
    assert_ne!(refreshed.identity(), first_identity);
    assert_eq!(refreshed.export().profile.compilation_command, changed);

    let command_string = Project::new();
    let arguments = command_string.compilation_arguments();
    command_string.write_compilation_database_command_string(&arguments.join(" "));
    refresh_import(&command_string.config()).expect("parse a CMake-style command string entry");
    assert_eq!(
        load_import(&command_string.config())
            .unwrap()
            .export()
            .profile
            .compilation_command,
        arguments
    );

    let missing = Project::new();
    missing.write_compilation_database_commands(&[]);
    let error = refresh_import(&missing.config()).unwrap_err();
    assert!(error.contains("has no command"), "{error}");
    assert!(!missing.artifact().exists());

    let ambiguous = Project::new();
    let command = ambiguous.compilation_arguments();
    ambiguous.write_compilation_database_commands(&[command.clone(), command]);
    let error = refresh_import(&ambiguous.config()).unwrap_err();
    assert!(error.contains("exactly one is required"), "{error}");
    assert!(!ambiguous.artifact().exists());

    let wrong_driver = Project::new();
    let mut command = wrong_driver.compilation_arguments();
    command[0] = "g++".into();
    wrong_driver.write_compilation_database_commands(&[command]);
    let error = refresh_import(&wrong_driver.config()).unwrap_err();
    assert!(error.contains("pinned Clang driver"), "{error}");
    assert!(!wrong_driver.artifact().exists());

    for untracked in ["@flags.rsp", "-include-pch", "-ivfsoverlay"] {
        let project = Project::new();
        let mut command = project.compilation_arguments();
        command.insert(1, untracked.into());
        project.write_compilation_database_commands(&[command]);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(
            error.contains("untracked preprocessor input mode"),
            "{error}"
        );
        assert!(!project.artifact().exists());
    }

    let wrong_standard = Project::new();
    let command = wrong_standard
        .compilation_arguments()
        .into_iter()
        .map(|argument| {
            if argument == "-std=c++20" {
                "-std=gnu++20".into()
            } else {
                argument
            }
        })
        .collect::<Vec<_>>();
    wrong_standard.write_compilation_database_commands(&[command]);
    let error = refresh_import(&wrong_standard.config()).unwrap_err();
    assert!(
        error.contains("profile must match the configured"),
        "{error}"
    );
    assert!(!wrong_standard.artifact().exists());

    let wrong_target = Project::new();
    let command = wrong_target
        .compilation_arguments()
        .into_iter()
        .map(|argument| {
            if argument == "--target=x86_64-unknown-linux-gnu" {
                "--target=aarch64-unknown-linux-gnu".into()
            } else {
                argument
            }
        })
        .collect::<Vec<_>>();
    wrong_target.write_compilation_database_commands(&[command]);
    let error = refresh_import(&wrong_target.config()).unwrap_err();
    assert!(
        error.contains("profile must match the configured"),
        "{error}"
    );
    assert!(!wrong_target.artifact().exists());
}

#[test]
fn included_header_definition_is_selected_locked_and_validated() {
    let project = Project::header_function();
    refresh_import(&project.config()).expect("export the selected header definition");
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    assert_eq!(lock["logical_source_sha256"].as_str().unwrap().len(), 64);

    let prepared = load_import(&project.config()).expect("load the locked header definition");
    assert_eq!(prepared.logical_source(), "selected.h");
    assert_eq!(prepared.export().logical_source, "selected.h");
    assert_eq!(prepared.export().profile.compilation_file, "driver.cpp");
    assert_eq!(prepared.export().function.name, "header_increment");
    assert_eq!(prepared.export().function.span.file, "selected.h");

    let sidecar = project.directory.join("demo.click");
    let sidecar_source = SIDECAR
        .replace("increment.cpp", "selected.h")
        .replace("increment", "header_increment");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let inputs = read_c_inputs(&sidecar, &sidecar_source).expect("load the header import offline");
    let CInput::PreparedProgram(import) = inputs else {
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
    assert!(!prepared.export().function.declared_noexcept);
    assert!(prepared.export().records.is_empty());

    let sidecar = project.directory.join("demo.click");
    let sidecar_source = SIDECAR
        .replace("increment.cpp", "selected.h")
        .replace("increment", "header_increment");
    fs::write(&sidecar, &sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");
    let inputs = read_c_inputs(&sidecar, &sidecar_source)
        .expect("load the exception-enabled header import offline");
    let CInput::PreparedProgram(import) = inputs else {
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
    assert!(!graph.export().function.declared_noexcept);
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
        prepared.export().function.body.as_slice(),
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
    verify_program_prepared_project(&rewritten, &prepared)
        .expect("the expanded exceptional proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&rewritten, &prepared)
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
    ] = prepared.export().function.body.as_slice()
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
            && returned_proof.contains("normalize();")
            && threw_proof.contains("assumption();")
            && !threw_proof.contains("normalize();")
            && !expanded.contains("trivial();"),
        "distinct exact path closers should retain returned/threw certificates: {expanded}"
    );
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &prepared)
        .expect("the expanded handler proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&rewritten, &prepared)
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
        prepared.export().function.body.as_slice(),
        [CppStatement::If { then_branch, else_branch, .. }, CppStatement::Return { .. }]
            if matches!(then_branch.as_slice(), [CppStatement::TryCatchInt32 { .. }])
                && else_branch.is_empty()
    ));

    let sidecar_source = r#"verifying "caller.cpp";
        void Restore_constructor(struct Restore* this, int32* slot) {
            owns this->pointer;
            owns this->saved;
            owns slot[0..1];
            ensures this->pointer == slot;
            ensures this->saved == old(slot[0]);
            ensures slot[0] == 9;
            ensures separate(memory(*this), memory(this->pointer[0..1]));
        } by { execute(); simp(); }
        void Restore_destructor(struct Restore* this) {
            requires separate(memory(*this), memory(this->pointer[0..1]));
            owns this->pointer;
            owns this->saved;
            owns this->pointer[0..1];
            ensures this->pointer == old(this->pointer);
            ensures this->saved == old(this->saved);
            ensures this->pointer[0] == old(this->saved);
        } by { execute(); simp(); }
        int32 helper(bool should_throw) throws int32 {
            ensures result == 5;
            exceptional ensures exception == 7;
        }
        int32 caller(int32& value, bool construct, bool should_throw) {
            owns value;
            ensures result == old(value);
            ensures value == old(value);
        } by {
            branch then {
                step();
                step();
                outcomes {
                    returned => { step(); step(); }
                    threw => { step(); execute(); simp(); }
                }
            } else { }
            step();
            simp();
        }
"#;
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, sidecar_source).unwrap();
    fs::remove_file(&project.exporter).expect("verification must use the locked artifact");
    let click_project = read_click_project(&sidecar, sidecar_source).unwrap();
    verify_program_prepared_project(&click_project, &prepared)
        .expect("the mixed conditional cleanup join should verify");
    let expanded = expand_project_claim_source_by_label(
        &click_project,
        &ProgramInputs::program(&prepared),
        "caller.contract",
    )
    .expect("expand the mixed outcome proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &prepared)
        .expect("the expanded mixed outcome proof must reverify");
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&click_project, &prepared)
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
#[ignore = "nightly: live C++ exporter scaling rechecks measured 34s"]
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
        let calls = "read(value);\n".repeat(size);
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
int32 read(int32& value) {{ owns value; ensures result == old(value); ensures value == old(value); }} by {{ execute(); simp(); }}
int32 many({parameters}, int32& value) {{ owns value; requires value == 7; ensures result == 7; ensures value == 7; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
        // Refuse the false result with a simple closer, rather than spending
        // the smart search budget trying to synthesize an impossible proof.
        let hostile = source
            .replace("ensures result == 7;", "ensures result == 8;")
            .replace(
                "ensures value == 7; } by { execute(); simp(); }",
                "ensures value == 7; } by { execute(); assumption(); }",
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
    verify_program_prepared_project(&parsed, &import).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "caller.ensures_0",
    )
    .unwrap();
    let rewritten = parsed.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import).unwrap();
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
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
fn scalar_int32_profile_unwinds_one_guard_on_both_paths() {
    let mdtest = parse_mdtest(
        Path::new("cpp_one_guard_unwind.md"),
        ONE_GUARD_UNWIND_MDTEST,
    )
    .unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let sidecar_source = mdtest.click_source.unwrap();
    let project = Project::with_fixture(&cpp.filename, &cpp.function, &cpp.source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(&cpp.function, &cpp.filename, true, &cpp.profile);
    refresh_import(&project.config()).expect("export a guard local to the try block");
    let prepared = load_import(&project.config()).expect("load the guard artifact offline");
    let [
        CppStatement::TryCatchInt32 { try_body, .. },
        CppStatement::Return { .. },
    ] = prepared.export().function.body.as_slice()
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
        statement: &'a CStatement,
        edges: &mut Vec<(&'a CStatement, &'a CStatement)>,
    ) {
        match statement {
            CStatement::TryCatchInt32 {
                try_body,
                handler,
                cleanup_unwind: true,
                ..
            } => {
                edges.push((try_body, handler));
                collect_unwind_edges(try_body, edges);
                collect_unwind_edges(handler, edges);
            }
            CStatement::Seq(first, second) => {
                collect_unwind_edges(first, edges);
                collect_unwind_edges(second, edges);
            }
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_unwind_edges(then_branch, edges);
                collect_unwind_edges(else_branch, edges);
            }
            CStatement::TryCatchInt32 {
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
    for (_, handler) in &edges {
        assert!(
            matches!(handler, CStatement::Seq(cleanup, rethrow)
                if contains_call(cleanup, "Restore_destructor")
                    && matches!(rethrow.as_ref(), CStatement::Throw(_))),
            "each escaping edge must run the live destructor before rethrowing"
        );
    }
    assert!(
        edges
            .iter()
            .any(|(try_body, _)| matches!(try_body, CStatement::Throw(_)))
    );
    assert!(edges.iter().any(|(try_body, _)| {
        matches!(try_body, CStatement::Seq(declare, call)
            if matches!(declare.as_ref(), CStatement::Declare { name, .. } if name == "ignored")
                && matches!(call.as_ref(), CStatement::CallAssign { function_name, .. } if function_name == "helper"))
    }));
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn scalar_int32_profile_rejects_hostile_cleanup_proofs() {
    let mdtest = parse_mdtest(
        Path::new("cpp_guard_unwind_before_second.md"),
        GUARD_BEFORE_SECOND_MDTEST,
    )
    .unwrap();
    let cpp = mdtest.cpp_source.unwrap();
    let sidecar_source = mdtest.click_source.unwrap();
    let project = Project::with_fixture(&cpp.filename, &cpp.function, &cpp.source);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior(&cpp.function, &cpp.filename, true, &cpp.profile);
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
                "            step();\n            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                "            step();\n            step();\n            have first_cell == old(first_cell);\n            step();\n            step();\n            have second_cell == old(second_cell);",
                1,
            ),
            "the first guard cannot be restored before the second cleanup",
        ),
        (
            "omitted_cleanup",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                "            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                1,
            ),
            "a proof cannot omit a required destructor",
        ),
        // Each `step()` runs the next lowered statement, so a destructor runs
        // once however many steps a proof writes: once both destructors and
        // the return have run, no step is left. One extra step only moves
        // the `have` past the first guard's destructor, where it still holds
        // and now verifies, since the caller's `second_cell` is kept
        // across that call although its value is not cached
        // (`mdtests/call_keeps_an_uncached_flat_field_beside_folded_state.md`).
        (
            "duplicated_cleanup",
            sidecar_source.replacen(
                "            step();\n            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                "            step();\n            step();\n            step();\n            step();\n            step();\n            step();\n            step();\n            have second_cell == old(second_cell);",
                1,
            ),
            "a proof cannot execute a destructor twice",
        ),
        (
            "unconstructed_second_guard",
            sidecar_source.replacen(
                "        threw => {\n            step();\n            have second_cell == old(second_cell);",
                "        threw => {\n            step();\n            step();\n            have second_cell == 9;",
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
        let project = Project::with_fixture(&cpp.filename, &cpp.function, &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(
            &cpp.function,
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
    for (name, source, expected) in [
        (
            "throwing_destructor",
            throwing_destructor,
            "has a non-throwing exception specification but can still throw",
        ),
        (
            "calling_destructor",
            calling_destructor,
            "noexcept C++ object operation",
        ),
    ] {
        let project = Project::with_fixture(&cpp.filename, &cpp.function, &source);
        project.write_exception_enabled_compilation_database();
        project.write_config_with_exception_behavior(
            &cpp.function,
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
    let error = refresh_import(&noexcept.config())
        .expect_err("the scalar profile must not mis-model noexcept termination");
    assert!(
        error.contains("does not model noexcept termination"),
        "{error}"
    );

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
    assert_eq!(import.export().schema, 60);
    assert!(import.export().profile.exceptions);
    assert!(!import.export().function.declared_noexcept);
    assert!(matches!(
        import.export().function.return_type,
        CppType::Boolean {
            bits: 8,
            is_const: false
        }
    ));
    let CppType::LvalueReference { pointee } = &import.export().function.parameters[0].value_type
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
        import.export().function.body.as_slice(),
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
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
    assert_eq!(
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Int64Pointer
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
    check_arithmetic_sidecar(&inequality, &import, &proof);

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
    assert_eq!(import.export().schema, 60);
    assert_eq!(import.export().dependencies, ["cstdint"]);
    let CppType::LvalueReference { pointee } = &import.export().function.parameters[0].value_type
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
        import.export().function.body.as_slice(),
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
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
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
    assert_eq!(import.export().schema, 60);
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
        import.export().function.body.as_slice(),
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
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
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
    assert_eq!(import.export().schema, 60);
    let [coin, max_money] = import.export().constants.as_slice() else {
        panic!("the upper-bound artifact lost the MAX_MONEY dependency graph")
    };
    assert_eq!(coin.name, "COIN");
    assert_eq!(max_money.name, "MAX_MONEY");
    assert!(matches!(
        import.export().function.body.as_slice(),
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
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
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
    assert_eq!(import.export().schema, 60);
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
    ] = import.export().function.body.as_slice()
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
    assert_eq!(lowered.kernel_function().return_type(), CType::Bool);
    assert!(matches!(lowered.kernel_function().body(),
        CStatement::Return(CExpression::Cast {
            expression,
            target_type: CType::Bool,
            ..
        }) if matches!(expression.as_ref(), CExpression::And(_, _))));
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
        error.contains("no reachable function definition"),
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
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_c_inputs(&sidecar, &click_source).expect("load the locked sidecar input");
    let CInput::PreparedProgram(import) = inputs else {
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
fn locked_cpp_branch_and_early_return_verify_through_the_shared_sidecar_path() {
    let project = Project::branch_return();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, BRANCH_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the branching C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load branching artifact offline");
    let source = &import.export().function;
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
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Bool
    );
    assert!(contains_if(lowered.kernel_function().body()));

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_c_inputs(&sidecar, &click_source).unwrap();
    let CInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify both C++ return paths against one contract");
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

    let sites = project_smart_tactic_source_sites(&click_project, &ProgramInputs::program(&import))
        .unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
    );
    let execute = project_tactic_source_position(
        &click_project,
        &ProgramInputs::program(&import),
        "choose.contract",
        0,
    )
    .unwrap();
    let expanded = expand_project_tactic_source_at(
        &click_project,
        &ProgramInputs::program(&import),
        execute.line,
        execute.column,
    )
    .expect("expand the branch execution into a checkable source proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the expanded branch proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the original branch verification environment");
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
fn const_reference_preserves_qualification_and_may_alias_a_mutable_reference() {
    let project = Project::const_reference_alias();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONST_REFERENCE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the const-reference C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let import = load_import(&project.config()).expect("load const-reference artifact offline");
    let source = &import.export().function;
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
    assert_eq!(parameters[0].c_type(), CType::Int32Pointer);
    assert!(!parameters[0].pointee_is_constant());
    assert_eq!(parameters[1].c_type(), CType::Int32Pointer);
    assert!(parameters[1].pointee_is_constant());

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_c_inputs(&sidecar, &click_source).unwrap();
    let CInput::PreparedProgram(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("one owned cell should authorize an aliased mutable write and const read");
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

    let sites = project_smart_tactic_source_sites(&click_project, &ProgramInputs::program(&import))
        .unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
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
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the const-reference verification environment");
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

fn contains_if(statement: &CStatement) -> bool {
    match statement {
        CStatement::If { .. } => true,
        CStatement::Seq(first, second) => contains_if(first) || contains_if(second),
        _ => false,
    }
}

fn contains_call(statement: &CStatement, expected: &str) -> bool {
    match statement {
        CStatement::Call { function_name, .. } | CStatement::CallAssign { function_name, .. } => {
            function_name == expected
        }
        CStatement::Seq(first, second) => {
            contains_call(first, expected) || contains_call(second, expected)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => contains_call(then_branch, expected) || contains_call(else_branch, expected),
        _ => false,
    }
}

fn call_order(statement: &CStatement) -> Vec<&str> {
    fn visit<'a>(statement: &'a CStatement, calls: &mut Vec<&'a str>) {
        match statement {
            CStatement::Call { function_name, .. } => calls.push(function_name),
            CStatement::Seq(first, second) => {
                visit(first, calls);
                visit(second, calls);
            }
            CStatement::If {
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

fn destructor_object_order<'a>(statement: &'a CStatement, destructor: &str) -> Vec<&'a str> {
    fn visit<'a>(statement: &'a CStatement, destructor: &str, objects: &mut Vec<&'a str>) {
        match statement {
            CStatement::Call {
                function_name,
                arguments,
            } if function_name == destructor => {
                if let [CExpression::Cast { expression, .. }] = arguments.as_slice()
                    && let CExpression::Variable(name) = expression.as_ref()
                {
                    objects.push(name);
                }
            }
            CStatement::Seq(first, second) => {
                visit(first, destructor, objects);
                visit(second, destructor, objects);
            }
            CStatement::If {
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

fn contains_raw_aggregate_destination(statement: &CStatement, expected: &str) -> bool {
    match statement {
        CStatement::DeclareAggregate {
            name,
            kind: click::kernel::CAggregateDeclarationKind::ConstructionDestination,
            ..
        } => name == expected,
        CStatement::Seq(first, second) => {
            contains_raw_aggregate_destination(first, expected)
                || contains_raw_aggregate_destination(second, expected)
        }
        CStatement::If {
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
    statement: &CStatement,
    call_local: &str,
    value_local: &str,
    callee: &str,
) -> [bool; 4] {
    let mut found = [false; 4];
    fn visit(
        statement: &CStatement,
        call_local: &str,
        value_local: &str,
        callee: &str,
        found: &mut [bool; 4],
    ) {
        match statement {
            CStatement::Declare {
                name,
                c_type: CType::Int32,
                ..
            } if name == call_local => found[0] = true,
            CStatement::CallAssign {
                target,
                function_name,
                ..
            } if target == call_local && function_name == callee => found[1] = true,
            CStatement::Declare {
                name,
                c_type: CType::Int32,
                ..
            } if name == value_local => found[2] = true,
            CStatement::Assign { name, .. } if name == value_local => found[3] = true,
            CStatement::Seq(first, second) => {
                visit(first, call_local, value_local, callee, found);
                visit(second, call_local, value_local, callee, found);
            }
            CStatement::If {
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

fn contains_local_aggregate_pipeline(statement: &CStatement, local: &str) -> [bool; 3] {
    let mut found = [false; 3];
    fn visit(statement: &CStatement, local: &str, found: &mut [bool; 3]) {
        match statement {
            CStatement::DeclareAggregate { name, layout, .. } if name == local => {
                found[0] = layout.size_bytes() == 16
                    && layout.alignment_bytes() == 8
                    && layout.fields().len() == 2;
            }
            CStatement::TypedStore {
                pointer,
                value_type,
                ..
            } => {
                if matches!(pointer, CExpression::Variable(name) if name == local)
                    && *value_type == CType::Int32Pointer
                {
                    found[1] = true;
                }
                if let CExpression::MemberAddress { object, selection } = pointer
                    && matches!(object.as_ref(), CExpression::Variable(name) if name == local)
                    && selection.value_type() == *value_type
                    && let [name] = selection.path()
                    && let Some(field) = selection
                        .layout()
                        .fields()
                        .iter()
                        .find(|field| field.name() == name)
                    && field.c_type() == *value_type
                {
                    if field.offset_bytes() == 0 && *value_type == CType::Int32Pointer {
                        found[1] = true;
                    }
                    if field.offset_bytes() == 8 && *value_type == CType::Int32 {
                        found[2] = true;
                    }
                }
                if let CExpression::PointerOffsetBytes { pointer, bytes } = pointer
                    && matches!(pointer.as_ref(), CExpression::Variable(name) if name == local)
                {
                    if *bytes == 0 && *value_type == CType::Int32Pointer {
                        found[1] = true;
                    }
                    if *bytes == 8 && *value_type == CType::Int32 {
                        found[2] = true;
                    }
                }
            }
            CStatement::Seq(first, second) => {
                visit(first, local, found);
                visit(second, local, found);
            }
            CStatement::If {
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
fn direct_cpp_call_exports_reachable_definition_and_verifies_modularly_offline() {
    let project = Project::direct_call();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, DIRECT_CALL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the resolved C++ call graph");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the call graph artifact offline");
    assert_eq!(import.export().schema, 60);
    assert_eq!(import.export().function.name, "call_set_seven");
    assert_eq!(import.export().reachable_functions.len(), 1);
    let reachable = &import.export().reachable_functions[0];
    assert_eq!(reachable.name, "set_seven");
    let CppStatement::Call {
        callee, arguments, ..
    } = &import.export().function.body[0]
    else {
        panic!("first caller operation was not a resolved call")
    };
    assert_eq!(callee.declaration_id, reachable.declaration_id);
    assert!(matches!(
        arguments.as_slice(),
        [CppCallArgument::Reference { place }]
            if place.declaration_id == import.export().function.parameters[0].declaration_id
    ));

    let lowered = lower_import(&import).expect("lower both C++ functions directly");
    assert!(contains_call(lowered.kernel_function().body(), "set_seven"));
    assert_eq!(lowered.reachable_kernel_functions().len(), 1);
    assert_eq!(lowered.reachable_kernel_functions()[0].name(), "set_seven");

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify the helper and caller through shared modular call rules");
    assert_eq!(verified.len(), 6);

    let sites = project_smart_tactic_source_sites(&click_project, &ProgramInputs::program(&import))
        .unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp", "execute", "simp"]
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
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the modular C++ verification environment");
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
fn scalar_local_captures_a_direct_call_result_and_verifies_offline() {
    let project = Project::scalar_local();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SCALAR_LOCAL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the typed C++ local and call result");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the scalar-local artifact offline");
    assert_eq!(import.export().schema, 60);
    assert_eq!(import.export().function.name, "relay_value");
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
    ] = import.export().function.body.as_slice()
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
    let verified = verify_program_prepared_project(&click_project, &import)
        .expect("verify local initialization through the shared call-result rule");
    assert_eq!(verified.len(), 5);

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
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
        .expect("retain the scalar-local verification environment");
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
fn mutable_pointer_dereference_and_reference_address_verify_offline() {
    let project = Project::pointer();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, POINTER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export pointer operations and the resolved call");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the pointer artifact offline");
    assert_eq!(import.export().schema, 60);
    let caller = &import.export().function;
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
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[0].c_type(),
        CType::Int32Pointer
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
fn record_reference_member_loads_and_stores_verify_offline() {
    let project = Project::struct_member();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, STRUCT_MEMBER_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the resolved C++ record layout and fields");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the record artifact offline");
    assert_eq!(import.export().schema, 60);
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

    let function = &import.export().function;
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
        lowered.kernel_function().parameters()[0].c_type(),
        CType::Int32Pointer
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
fn brace_initialized_local_aggregate_verifies_offline() {
    let project = Project::local_aggregate();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, LOCAL_AGGREGATE_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the local aggregate initializer");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the aggregate artifact offline");
    assert_eq!(import.export().schema, 60);
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
    ] = import.export().function.body.as_slice()
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
fn explicit_constructor_local_verifies_as_a_modular_call() {
    let project = Project::constructor_local();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, CONSTRUCTOR_LOCAL_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export the direct constructor call and body");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the constructor artifact offline");
    assert_eq!(import.export().schema, 60);
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
    ] = import.export().function.body.as_slice()
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
        "RestoreState_constructor"
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
        lowered.reachable_kernel_functions()[0].parameters()[0].c_type(),
        CType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].parameters()[1].c_type(),
        CType::Int32Pointer
    );
    assert_eq!(
        lowered.reachable_kernel_functions()[0].return_type(),
        CType::Void
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
#[ignore = "nightly: 2s in the parallel gate"]
fn terminal_return_captures_value_before_checked_destructor_cleanup() {
    let project = Project::terminal_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, TERMINAL_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export constructor and terminal destructor cleanup");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the cleanup artifact offline");
    assert_eq!(import.export().schema, 60);
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
    ] = import.export().function.body.as_slice()
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
        ["RestoreState_constructor", "RestoreState_destructor"]
    );
    assert!(matches!(
        lowered.kernel_function().body(),
        CStatement::Seq(_, returned)
            if matches!(
                returned.as_ref(),
                CStatement::Seq(_, returned)
                    if matches!(
                        returned.as_ref(),
                        CStatement::Return(CExpression::Variable(name))
                            if name.starts_with("__click_cpp_return_value")
                    )
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
    verify_program_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("expanded terminal-cleanup proof must reverify");

    let missing_destructor = TERMINAL_DESTRUCTOR_SIDECAR.replace(
        "void RestoreState_destructor(struct RestoreState* this) {\n    requires separate(memory(*this), memory(this->pointer[0..1]));\n    owns this->pointer;\n    owns this->saved;\n    owns this->pointer[0..1];\n    ensures this->pointer == old(this->pointer);\n    ensures this->saved == old(this->saved);\n    ensures this->pointer[0] == old(this->saved);\n} by {\n    execute();\n    simp();\n}\n\n",
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
#[ignore = "nightly: 3s in the parallel gate"]
fn every_return_after_construction_runs_the_checked_destructor() {
    let project = Project::early_return_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, EARLY_RETURN_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export cleanup on both C++ return edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the cleanup artifact offline");
    assert_eq!(import.export().schema, 60);
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
    ] = import.export().function.body.as_slice()
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
        [
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor"
        ]
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
        "ensures early != 0 implies result == 7;",
        "ensures early != 0 implies result == 9;",
    );
    fs::write(&sidecar, &wrong_early_result).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_early_result).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("cleanup must not overwrite the value captured by the early return");
}

#[test]
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
    assert_eq!(import.export().function.name, "call_with_restore");
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
    } = &import.export().function.body[0]
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
        "the captured call must remain a checked kernel call assignment"
    );

    let click_project = read_click_project(&sidecar, RESTORE_CALLER_SIDECAR).unwrap();
    verify_program_prepared_project(&click_project, &import)
        .expect("the caller must receive 7 or 9 and still own an unchanged 41");
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
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
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
#[ignore = "nightly: 3s in the parallel gate"]
fn two_constructed_objects_are_destroyed_in_reverse_order_on_every_return() {
    let project = Project::reverse_destructor_order();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, REVERSE_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export reverse cleanup on both C++ return edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the ordered cleanup artifact offline");
    assert_eq!(import.export().schema, 60);
    let [
        CppStatement::Declare { local: first, .. },
        CppStatement::Declare { local: second, .. },
        CppStatement::If { then_branch, .. },
        CppStatement::Assign { .. },
        CppStatement::Return {
            cleanups: final_cleanups,
            ..
        },
    ] = import.export().function.body.as_slice()
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
        destructor_object_order(lowered.kernel_function().body(), "Restore_destructor"),
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
            "Restore_destructor"
        ),
        ["third", "second", "first", "third", "second", "first"]
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn nested_scope_destroys_its_object_on_return_and_fallthrough() {
    let project = Project::nested_scope_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, NESTED_SCOPE_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export both nested-scope cleanup edges");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the nested-scope artifact offline");
    assert_eq!(import.export().schema, 60);
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
    ] = import.export().function.body.as_slice()
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
        destructor_object_order(lowered.kernel_function().body(), "Restore_destructor"),
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
        "ensures early == 0 implies result == old(value);",
        "ensures early == 0 implies result == 9;",
    );
    fs::write(&sidecar, &wrong_fallthrough).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_fallthrough).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("fallthrough destruction must occur before the outer return");
}

#[test]
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
    ] = import.export().function.body.as_slice()
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
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor",
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor",
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
        "second_early == 0 implies result == old(value)",
        "second_early == 0 implies result == 11",
    );
    fs::write(&sidecar, &wrong_final).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_final).unwrap();
    verify_program_prepared_project(&wrong_project, &import)
        .expect_err("the second scope must clean up before the final outer return");
}

#[test]
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
        growing_import
            .export()
            .function
            .body
            .iter()
            .filter(|statement| matches!(statement, CppStatement::Scope { .. }))
            .count(),
        3
    );
    let (contracts, _) = SIBLING_SCOPE_DESTRUCTORS_SIDECAR
        .rsplit_once("} by {")
        .unwrap();
    let proof = r#"step(); step();
    branch then { execute(); simp(); } else { }
    step(); step();
    have value == old(value) by { simp(); }
    step(); step();
    branch then { execute(); simp(); } else { }
    step(); step();
    have value == old(value) by { simp(); }
    step(); step(); step(); step();
    have value == old(value) by { simp(); }
    execute(); simp();"#;
    let source = format!("{contracts}}} by {{\n{proof}\n}}\n");
    check_return_call_sidecar(&growing, &growing_import, &source);
}

#[test]
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
    ] = import.export().function.body.as_slice()
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
        destructor_object_order(lowered.kernel_function().body(), "Restore_destructor"),
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
    ] = import.export().function.body.as_slice()
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
        [
            "Restore_constructor",
            "Restore_destructor",
            "Restore_destructor",
        ]
    );

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    verify_program_prepared_project(&click_project, &import).expect(
        "verify cleanup on constructed paths without calling the destructor on the skipped path",
    );

    let expanded = expand_project_claim_source_by_label(
        &click_project,
        &ProgramInputs::program(&import),
        "conditional_restore.contract",
    )
    .expect("fully expand the proof across the conditional lifetime");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_program_prepared_project(&rewritten, &import)
        .expect("the fully expanded conditional-construction proof must reverify");
    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
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
        "ensures construct == 0 implies result == 41;",
        "ensures construct == 0 implies result == 7;",
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
fn terminal_destructor_rejects_throwing_virtual_empty_and_nonterminal_cleanup() {
    let project = Project::terminal_destructor();
    for (source, expected) in [
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "~RestoreState() noexcept",
                "~RestoreState() noexcept(false)",
            ),
            "public, non-virtual, non-deleted, and explicitly noexcept",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace("~RestoreState() noexcept", "~RestoreState()"),
            "public, non-virtual, non-deleted, and explicitly noexcept",
        ),
        (
            TERMINAL_DESTRUCTOR_SOURCE.replace(
                "~RestoreState() noexcept",
                "virtual ~RestoreState() noexcept",
            ),
            "standard-layout",
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
}} by {{ execute(); simp(); }}
"#
        );
        check_arithmetic_sidecar(&project, &import, &sidecar);
        let hostile = sidecar.replace(" owns data[0..3];", "");
        let path = project.directory.join("bad.click");
        fs::write(&path, &hostile).unwrap();
        let parsed = read_click_project(&path, &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
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
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, fixed_index);
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
}} by {{ execute(); simp(); }}
"#
        );
        check_arithmetic_sidecar(&project, &import, &sidecar);
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
}} by {{ execute(); simp(); }}
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
    assert!(error.contains("mutable int* parameter"), "{error}");
    assert!(!project.artifact().exists());
}

#[test]
fn cpp_record_slice_rejects_unresolved_methods_bitfields_and_inheritance() {
    let project = Project::struct_member();

    fs::write(
        project.source(),
        "struct RestoreState {\n    int saved;\n    int read() noexcept;\n};\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    state.read();\n    return state.saved;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("no reachable function definition"),
        "{error}"
    );
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
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "stage_restore.cpp";
int32 stage_restore(struct First& first, struct Second& second) {
 owns first.value; owns second.value;
 ensures result == old(second.value); ensures first.value == old(second.value);
} by { execute(); simp(); }
"#,
    );
}

#[test]
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
        vec!["execute", "simp"]
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

    let (session, _) = C0VerificationSession::new_program_prepared_project(&click_project, &import)
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

    // A fact about the referent names it as the sidecar does.
    let false_claim = refusal(&SIDECAR.replace(
        "ensures value == old(value) + 1;",
        "ensures value == old(value) + 2;",
    ));
    assert!(
        false_claim.contains("left side evaluated to (value + 1)"),
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
    let declaration_id = prepared.export().function.declaration_id.clone();
    let function_span = prepared.export().function.span.clone();
    let lowered = lower_import(&prepared).expect("lower the typed artifact directly");

    assert_eq!(lowered.source().identity(), prepared.identity());
    assert_eq!(lowered.source_function().declaration_id, declaration_id);
    assert_eq!(lowered.source_function().span, function_span);
    let function = lowered.kernel_function();
    assert_eq!(function.name(), "increment");
    assert_eq!(function.return_type(), CType::Int32);
    assert_eq!(function.parameters().len(), 1);
    assert_eq!(function.parameters()[0].name(), "&value");
    assert_eq!(function.parameters()[0].c_type(), CType::Int32Pointer);
    assert!(matches!(
        function.body(),
        CStatement::Seq(store, returned)
            if matches!(
                store.as_ref(),
                CStatement::TypedStore {
                    pointer: CExpression::Variable(pointer),
                    value: CExpression::Add(left, right),
                    value_type: CType::Int32,
                    volatile: false,
                    pointee_constant: false,
                } if pointer == "&value"
                    && matches!(
                        left.as_ref(),
                        CExpression::TypedLoad {
                            pointer,
                            value_type: CType::Int32,
                            volatile: false,
                            ..
                        } if matches!(pointer.as_ref(), CExpression::Variable(name) if name == "&value")
                    )
                    && matches!(right.as_ref(), CExpression::Value(value) if value == &int32(1))
            )
            && matches!(
                returned.as_ref(),
                CStatement::Return(CExpression::TypedLoad {
                    pointer,
                    value_type: CType::Int32,
                    volatile: false,
                    ..
                }) if matches!(pointer.as_ref(), CExpression::Variable(name) if name == "&value")
            )
    ));

    // A native reference receives the complete address formed from a real
    // scalar declaration. A typed numeric address alone supplies no referent.
    let normal_state = |state: CState, statement: CStatement| {
        let theorem = click::kernel::prove_c_statement_execution(state, statement)
            .expect("checked scalar setup should execute");
        let Proposition::CStatementExecutes {
            outcome: click::kernel::CStatementOutcome::Normal(state),
            ..
        } = theorem.proposition()
        else {
            panic!(
                "expected unconditional normal setup: {:?}",
                theorem.proposition()
            );
        };
        state.as_ref().clone()
    };
    let state = normal_state(
        CState::new(),
        click::kernel::c_declare_initialized(
            "referent",
            CType::Int32,
            CExpression::Value(int32(41)),
            false,
            false,
            false,
            false,
        ),
    );
    let address = click::kernel::prove_c_expression_evaluation(
        state.clone(),
        click::kernel::c_addr_of("referent"),
    )
    .expect("checked address formation should select the declared scalar");
    let Proposition::CExpressionEvaluates {
        outcome: click::kernel::CExpressionOutcome::Value(value),
        ..
    } = address.proposition()
    else {
        panic!(
            "expected a declared scalar address: {:?}",
            address.proposition()
        );
    };
    let arguments = vec![CExpression::Value(value.clone())];
    // This fixture checks the call's referent storage; its declaration's local
    // name belongs to the setup frame, rather than the tested caller frame.
    let state = CState::new()
        .with_memory(state.memory().clone())
        .with_resource_context(state.resources().clone());
    let expected_state = normal_state(
        state.clone(),
        click::kernel::c_typed_store(
            arguments[0].clone(),
            CExpression::Value(int32(42)),
            CType::Int32,
        ),
    );
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("the lowered reference function should execute");
    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state: Box::new(state.clone()),
            function: Box::new(function.clone()),
            arguments: arguments.clone(),
            outcome: CFunctionOutcome::Return {
                value: int32(42),
                state: Box::new(expected_state),
            },
        }
    );

    let max_state = normal_state(
        state,
        click::kernel::c_typed_store(
            arguments[0].clone(),
            CExpression::Value(int32(i32::MAX as u32)),
            CType::Int32,
        ),
    );
    let overflow = prove_symbolic_c_function_execution(
        max_state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
    )
    .expect("concrete signed overflow should produce a checked outcome");
    assert_eq!(
        overflow.proposition(),
        &Proposition::CFunctionExecutes {
            state: Box::new(max_state),
            function: Box::new(function.clone()),
            arguments,
            outcome: CFunctionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
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
    assert!(error.contains("config"), "{error}");

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
        "int increment(const int* value) noexcept {\n    return *value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("mutable int* parameter"), "{error}");
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
        import.export().function.return_type,
        CppType::Enumeration {
            is_scoped: true,
            is_fixed: true,
            ..
        }
    ));
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint8 echo(uint8 value) { ensures result == value; } by { execute(); simp(); } uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }",
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
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint8 probe(uint32 value) { requires value == 511u32; ensures result == 255u8; } by { execute(); simp(); }",
    );
}

#[test]
fn cpp_fixed_byte_enum_converted_call_results_verify_offline() {
    let project = Project::with_fixture(
        "enum.cpp",
        "probe",
        "enum class Byte : unsigned char {}; unsigned int echo(unsigned int value) noexcept { return value; } Byte probe(unsigned int value) noexcept { return static_cast<Byte>(echo(value)); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint32 echo(uint32 value) { ensures result == value; } by { execute(); simp(); } uint8 probe(uint32 value) { requires value == 511u32; ensures result == 255u8; } by { execute(); simp(); }",
    );
}

#[test]
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
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"enum.cpp\"; uint8 echo(uint8 value) { ensures result == value; } by { execute(); simp(); } uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }",
    );
    let artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    for mutation in 0..4 {
        let mut forged = artifact.clone();
        let cast = &mut forged["function"]["body"][0]["conversions"][0];
        match mutation {
            0 => cast["cast_kind"] = "no_op".into(),
            1 => cast["cast_kind"] = "integral_cast".into(),
            2 => cast["explicit"] = false.into(),
            3 => cast["source_type"]["declaration_id"] = "c:@E@Other".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
        let ty = &mut forged["function"]["body"][0]["value"]["value_type"];
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"bytes.cpp\"; uint8 echo(uint8 value) { ensures result == value; } by { execute(); simp(); } uint8 probe(uint8 value) { ensures result == value; } by { execute(); simp(); }",
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
    let proof = "verifying \"bytes.cpp\"; uint8 probe(uint32 value) { requires value == 511u32; ensures result == 255u8; } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, proof);
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
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"bytes.cpp\"; uint32 probe(uint8 value) { requires value == 255u8; ensures result == 65025u32; } by { execute(); simp(); }",
    );
}

#[test]
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
    let proof = "verifying \"bytes.cpp\"; uint8 probe(struct Bytes& bytes, uint8 value) { owns bytes.first; views bytes.second; views bytes.tail; ensures bytes.first == value; ensures result == old(bytes.second); ensures bytes.second == old(bytes.second); ensures bytes.tail == old(bytes.tail); } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, proof);
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
        import.export().function.body[0],
        CppStatement::Declare {
            initializer: CppInitializer::Uninitialized,
            ..
        }
    ));
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"uninitialized.cpp\"; uint32 probe(uint32 value) { ensures result == value; } by { execute(); simp(); }",
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
    let source = "verifying \"uninitialized.cpp\"; uint32 probe() { ensures result == result; } by { execute(); simp(); }";
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
        artifact["function"]["body"][0]["initializer"] =
            serde_json::json!({"kind":"uninitialized"});
        let bytes = serde_json::to_vec_pretty(&artifact).unwrap();
        let mut lock: serde_json::Value =
            serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
        "int set_seven(int& value) noexcept;\n\nint call_set_seven(int& value) noexcept {\n    set_seven(value);\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("call_set_seven.cpp:4"), "{error}");
    assert!(
        error.contains("no reachable function definition"),
        "{error}"
    );
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
fn cpp_config_rejects_profiles_outside_the_pinned_slice() {
    let project = Project::new();
    let bytes = fs::read_to_string(project.config()).unwrap();
    fs::write(project.config(), bytes.replace("c++20", "gnu++20")).unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("Clang c++20"), "{error}");

    let mismatch = Project::new();
    mismatch.write_config_with_profile("increment", "increment.cpp", true);
    let error = refresh_import(&mismatch.config()).unwrap_err();
    assert!(
        error.contains("profile must match the configured"),
        "{error}"
    );
    assert!(!mismatch.artifact().exists());
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
        verify_program_prepared_project(&parsed, &import)
            .unwrap_or_else(|error| panic!("{selected}: {}", error.message()));
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
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let next_sites =
            project_smart_tactic_source_sites(&rewritten, &ProgramInputs::program(&import))
                .unwrap();
        let next = next_sites.first().unwrap();
        let next = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            &next.claim_label,
            next.source_index,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, next.line, next.column)
            .expect("audit session checks the expanded method proof");
    }
}

#[test]
fn value_methods_reject_false_claims_missing_authority_and_overflow() {
    let source = include_str!("fixtures/cpp-verification/value-methods/value_methods.cpp");
    let add = include_str!("fixtures/cpp-verification/value-methods/add_disjoint.click");
    let empty = include_str!("fixtures/cpp-verification/value-methods/is_empty.click");
    for (selector, proof, expected) in [
        ("FeeFrac::IsEmpty", empty.replace("if old(this->size) == 0", "if old(this->size) == 1"), "unclosed goal"),
        // The receiver is the pointer `this`; the older `self` does not match.
        ("FeeFrac::IsEmpty", empty.replace("this", "self"), ".click has const struct FeeFrac* self, C has const struct FeeFrac* this"),
        ("FeeFrac::operator+=", add.replace("ensures this->fee == old(this->fee) + old(other.fee);", "ensures this->fee == old(this->fee);"), "unclosed goal"),
        ("FeeFrac::operator+=", add.replace("    owns this->fee;\n", ""), "missing resource fact"),
        ("FeeFrac::operator+=", add.replace("    requires -4611686018427387904 <= this->fee;\n    requires this->fee <= 4611686018427387903;\n", ""), "overflow"),
        ("FeeFrac::operator+=", add.replace("    requires -1073741824 <= this->size;\n    requires this->size <= 1073741823;\n", ""), "overflow"),
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

fn check_arithmetic_sidecar(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    check_sidecar_tactic(project, import, source, None);
}

fn check_return_call_sidecar(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
) {
    let prefix = format!("{}.", import.export().function.name);
    check_sidecar_tactic(project, import, source, Some(&prefix));
}

fn check_sidecar_tactic(
    project: &Project,
    import: &click::languages::cpp::PreparedCppImport,
    source: &str,
    claim_prefix: Option<&str>,
) {
    let sidecar = project.directory.join("arithmetic.click");
    let source = source.replace(
        "-9223372036854775808i64",
        "(-9223372036854775807i64 - 1i64)",
    );
    fs::write(&sidecar, &source).unwrap();
    let parsed = read_click_project(&sidecar, &source).unwrap();
    verify_program_prepared_project(&parsed, import)
        .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
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
        panic!(
            "expanded arithmetic certificate: {}\n{expanded}",
            error.message()
        )
    });
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&parsed, import).unwrap();
    let sites =
        project_smart_tactic_source_sites(&rewritten, &ProgramInputs::program(import)).unwrap();
    let first = match claim_prefix {
        Some(prefix) => sites
            .iter()
            .find(|site| site.claim_label.starts_with(prefix))
            .expect("selected caller tactic"),
        None => sites.first().unwrap(),
    };
    let position = project_tactic_source_position(
        &rewritten,
        &ProgramInputs::program(import),
        &first.claim_label,
        first.source_index,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .expect("retained audit accepts arithmetic certificate");
}

#[test]
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
            "verifying \"arithmetic.cpp\";\nint64 rounded_divide(int64 n, int32 d, bool round_down) {{\nrequires n == {n}i64;\nrequires d == {d};\nrequires round_down == {};\nensures result == {result}i64;\n}} by {{ execute(); simp(); }}\n",
            i32::from(down)
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
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
            "requires n == -7i64; requires d == 3; requires round_down == 1;",
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
            "verifying \"arithmetic.cpp\";\nint64 {selector}({parameters}) {{ {preconditions} ensures {claim}; }} by {{ execute(); simp(); }}\n"
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
            "1",
        ),
        (
            "truth",
            "bool truth(long n) noexcept { return bool(n); }",
            "int64 n",
            "requires n == 0i64;",
            "bool",
            "0",
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
            "verifying \"arithmetic.cpp\";\n{result_type} {selector}({parameters}) {{ {preconditions} ensures result == {expected}; }} by {{ execute(); simp(); }}\n"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
    let project = Project::with_fixture(
        "arithmetic.cpp",
        "relay",
        "long quotient(long n, long d) noexcept { return n / d; }\nlong relay(long n, long d, int& untouched) noexcept { int captured = quotient(n, d); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "arithmetic.cpp";
int64 quotient(int64 n, int64 d) {
 requires n == 4294967297i64; requires d == 1i64;
 ensures result == 4294967297i64;
} by { execute(); simp(); }
int64 relay(int64 n, int64 d, int32& untouched) {
 views untouched;
 requires n == 4294967297i64; requires d == 1i64;
 ensures result == 1i64; ensures untouched == old(untouched);
} by { execute(); simp(); }
"#,
    );
}

#[test]
fn subtraction_method_self_aliasing_is_defined_without_bounds_and_frames_caller_memory() {
    let project = Project::with_fixture(
        "subtract_methods.cpp",
        "clear_value",
        include_str!("fixtures/cpp-verification/subtract-methods/subtract_methods.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = include_str!("fixtures/cpp-verification/subtract-methods/clear_value.click");
    check_arithmetic_sidecar(&project, &import, proof);
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
    let CppType::Integer { source_aliases, .. } = &import.export().function.return_type else {
        panic!("missing signed return type")
    };
    assert_eq!(source_aliases[0].name, "int64_t");
    assert_eq!(source_aliases[0].span.file, "cstdint");
    check_arithmetic_sidecar(
        &project,
        &import,
        include_str!("fixtures/cpp-verification/signed-arithmetic/quotient.click"),
    );
}

const UNSIGNED_ARITHMETIC_SOURCE: &str =
    include_str!("fixtures/cpp-verification/unsigned-arithmetic/arithmetic.cpp");

#[test]
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
            "1",
        ),
    ] {
        let project = Project::with_fixture("unsigned.cpp", name, UNSIGNED_ARITHMETIC_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"unsigned.cpp\";\n{result_type} {name}({params}) {{ {requires} ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn unsigned_modular_calls_frame_unrelated_memory_and_reject_false_wrap_claims() {
    let project = Project::with_fixture("unsigned.cpp", "relay", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "unsigned.cpp";
uint64 add64(uint64 a, uint64 b) { ensures result == a + b; } by { execute(); simp(); }
uint64 relay(uint64 a, uint64 b, int32& untouched) {
 owns untouched;
 ensures result == a + b;
 ensures untouched == old(untouched);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
    let project = Project::with_fixture("unsigned.cpp", "add64", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "unsigned.cpp";
uint64 add64(uint64 a, uint64 b) {
 requires a == 18446744073709551615u64; requires b == 1u64;
 ensures result == 1u64;
} by { execute(); simp(); }
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
            "verifying \"unsigned.cpp\"; uint64 {name}(uint64 a, uint64 b) {{ requires b == 0u64; ensures result == 0u64; }} by {{ execute(); simp(); }}"
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
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"constants.cpp\"; uint32 size() { ensures result == 10u32; } by { execute(); simp(); }",
    );
    let project = Project::with_fixture(
        "constants.cpp",
        "size",
        "unsigned long runtime() noexcept; unsigned long size() noexcept { return runtime(); }",
    );
    assert!(refresh_import(&project.config()).is_err());
    assert!(!project.artifact().exists());
}

#[test]
fn unsigned_positive_divisor_contract_expands_and_reverifies() {
    let project = Project::with_fixture("unsigned.cpp", "div64", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"unsigned.cpp\"; uint64 div64(uint64 a, uint64 b) { requires b > 0u64; ensures result == a / b; } by { execute(); simp(); }",
    );
}

#[test]
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
                "verifying \"fast_path.cpp\"; uint64 {name}(int64 fee, int32 at_size, int32 size) {{ requires fee == {fee}i64; requires at_size == {at_size}; requires size == {size}; ensures result == {expected}u64; }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &proof);
        }
    }
}

#[test]
fn mixed_unsigned_return_preserves_signed_intermediate_overflow() {
    let project = Project::with_fixture("unsigned.cpp", "mixed", UNSIGNED_ARITHMETIC_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = "verifying \"unsigned.cpp\"; uint64 mixed(int64 a, uint32 b) { requires a == 9223372036854775807i64; requires b == 4294967295u32; ensures result == 0u64; } by { execute(); simp(); }";
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
fn compiler_constant_calls_preserve_runtime_constant_evaluation_context() {
    // A constexpr function can distinguish constant evaluation from a runtime
    // call. The exporter must fold the latter meaning in an imported body.
    let cpp = "namespace std { template<class T> struct numeric_limits { static constexpr unsigned long max() noexcept { return __builtin_is_constant_evaluated() ? 1UL : 2UL; } }; } unsigned long probe() noexcept { return std::numeric_limits<unsigned long>::max(); }";
    let project = Project::with_fixture("constant_context.cpp", "probe", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"constant_context.cpp\"; uint64 probe() { ensures result == 2u64; } by { execute(); simp(); }",
    );
    let bad = "verifying \"constant_context.cpp\"; uint64 probe() { ensures result == 1u64; } by { execute(); simp(); }";
    fs::write(project.directory.join("bad.click"), bad).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), bad).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

const TEMPLATE_INSTANCE_SOURCE: &str =
    include_str!("fixtures/cpp-verification/template-instances/instances.cpp");

#[test]
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
int32 choose__bool_true(int32 a, int32 b) {
 requires a >= -1073741824; requires a <= 1073741823;
 ensures result == a; ensures result >= -1073741824; ensures result <= 1073741823;
} by { execute(); simp(); }
int32 choose__bool_false(int32 a, int32 b) {
 requires b >= -1073741824; requires b <= 1073741823;
 ensures result == b; ensures result >= -1073741824; ensures result <= 1073741823;
} by { execute(); simp(); }
int32 both(int32 a, int32 b, int32* untouched) {
 requires a >= -1073741824; requires a <= 1073741823;
 requires b >= -1073741824; requires b <= 1073741823;
 owns untouched[0..1];
 ensures result == a + b;
 ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let hostile = sidecar.replace("ensures result == b;", "ensures result == a;");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
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
int32 identity__int(int32 value) { ensures result == value; } by { execute(); simp(); }
uint64 identity__unsigned_long(uint64 value) { ensures result == value; } by { execute(); simp(); }
uint64 widths(int32 a, uint64 b) {
 requires a == 1; requires b == 18446744073709551615u64;
 ensures result == 0u64;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
}

#[test]
fn concrete_member_template_instances_preserve_receiver_authority() {
    let project = Project::with_fixture("instances.cpp", "member", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"verifying "instances.cpp";
int64 Value_select__bool_true(const struct Value* this) {
 views this->fee;
 ensures result == this->fee;
 ensures this->fee == old(this->fee);
} by { execute(); simp(); }
int64 Value_select__bool_false(const struct Value* this) {
 views this->fee;
 ensures result == 0i64;
 ensures this->fee == old(this->fee);
} by { execute(); simp(); }
int64 member(const struct Value& value) {
 owns value.fee;
 ensures result == value.fee;
 ensures value.fee == old(value.fee);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let hostile = sidecar.replace(" owns value.fee;", "");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
fn constexpr_discards_only_the_compiler_selected_arm() {
    let project = Project::with_fixture("instances.cpp", "accepted", TEMPLATE_INSTANCE_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().reachable_functions.len(), 1);
    let sidecar = r#"verifying "instances.cpp";
int32 bounded__bool_true(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 accepted(int32 value) { ensures result == value; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let rejected = Project::with_fixture("instances.cpp", "rejected", TEMPLATE_INSTANCE_SOURCE);
    let error = refresh_import(&rejected.config()).unwrap_err();
    assert!(
        error.contains("unsupported") || error.contains("reachable"),
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
    let source = r#"verifying "instances.cpp";
uint64 identity__unsigned_long(uint64 value) { ensures result == value; } by { execute(); simp(); }
uint64 identity__unsigned_long_long(uint64 value) { ensures result == value; } by { execute(); simp(); }
uint64 exact_types(uint64 a, uint64 b) { ensures result == a + b; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
}

#[test]
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
            "verifying \"instances.cpp\"; int32 {selected}({params}) {{ ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
    let project = Project::with_fixture("instances.cpp", "runtime_if", TEMPLATE_INSTANCE_SOURCE);
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(
        error.contains("no reachable function definition"),
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
int32 flag__bool_true() { ensures result == 1; } by { execute(); simp(); }
int32 get_flag() { ensures result == 1; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
}

#[test]
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
        sidecar.push_str(&format!(
            "int32 {name}(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}\n"
        ));
    }
    sidecar
        .push_str("int32 call(int32 value) { ensures result == value; } by { execute(); simp(); }");
    check_arithmetic_sidecar(&project, &import, &sidecar);
}

#[test]
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
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
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
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"defaulted.cpp\"; int32 read(int32 input) { ensures result == input; } by { execute(); simp(); }",
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
        error.contains("destructor must be public, non-virtual, non-deleted"),
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
#[ignore = "nightly: 5s in the parallel gate"]
fn instantiated_fee_fast_paths_preserve_both_rounding_expressions() {
    for (fee, at_size, size) in [
        (0u64, 1u64, 3u64),
        (7, 2, 3),
        (8, 2, 4),
        (8589934591, 2147483647, 2147483647),
    ] {
        for (selected, instance, expected) in [
            ("fee_down", "fee_fast_path__bool_true", fee * at_size / size),
            (
                "fee_up",
                "fee_fast_path__bool_false",
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
                "verifying \"instances.cpp\"; uint64 {instance}(int64 fee, int32 at_size, int32 size) {{ {contract} }} by {{ execute(); simp(); }} uint64 {selected}(int64 fee, int32 at_size, int32 size) {{ {contract} }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &source);
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
#[ignore = "nightly: 3s in the parallel gate"]
fn class_template_instances_preserve_nominal_identity_and_verify_offline() {
    let mut alias_identity = None;
    let mut identities = std::collections::BTreeSet::new();
    for (selected, record) in [
        ("call", "Box__int__bool_false"),
        ("wide", "Box__long_long__bool_false"),
        ("long_type", "Box__long__bool_false"),
        ("tagged", "Box__tag_SizeTag__bool_true"),
        ("other_tag", "Box__tag_WeightTag__bool_true"),
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
        let sidecar = format!(
            "verifying \"instances.cpp\"; int32 {record}_Read(const struct {record}* this) {{ views this->value; ensures result == this->value; }} by {{ execute(); simp(); }} int32 {selected}(const struct {record}& box) {{ views box.value; ensures result == box.value; }} by {{ execute(); simp(); }}"
        );
        fs::remove_file(&project.exporter).unwrap();
        check_return_call_sidecar(&project, &load_import(&project.config()).unwrap(), &sidecar);
    }
    let plain = Project::with_fixture("instances.cpp", "plain", CLASS_INSTANCE_SOURCE);
    refresh_import(&plain.config()).unwrap();
    assert_eq!(
        load_import(&plain.config()).unwrap().export().records[0].declaration_id,
        alias_identity.unwrap()
    );
}

#[test]
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
        void Stored__long_long_constructor(struct Stored__long_long* this, int64 next) {
            owns this->value; ensures this->value == next;
        } by { execute(); simp(); }
        int64 Stored__long_long_Read(const struct Stored__long_long* this) {
            views this->value; ensures result == this->value;
        } by { execute(); simp(); }
        void Stored__long_long_destructor(struct Stored__long_long* this) {
            owns this->value; ensures this->value == 0i64;
        } by { execute(); simp(); }
        int64 create(int64 next) {
            ensures result == next;
        } by { execute(); simp(); }
    "#;
        fs::remove_file(&project.exporter).unwrap();
        check_return_call_sidecar(
            &project,
            &import,
            &sidecar.replace("Stored__long_long", record),
        );
    }
}

#[test]
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
        int32 Box__tag_SizeTag__bool_true_Read(const struct Box__tag_SizeTag__bool_true* this) {
            views this->value; ensures result == this->value;
        } by { execute(); simp(); }
        int32 both(const struct Box__tag_SizeTag__bool_true& left,
                   const struct Box__tag_WeightTag__bool_true& right) {
            views left.value; views right.value;
            ensures result == left.value;
            ensures right.value == old(right.value);
        } by { execute(); simp(); }
    "#;
    fs::remove_file(&project.exporter).unwrap();
    check_return_call_sidecar(&project, &import, sidecar);
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
    let right = artifact["function"]["parameters"][1].clone();
    let place = &mut artifact["function"]["body"][0]["arguments"][0]["place"];
    place["declaration_id"] = right["declaration_id"].clone();
    place["name"] = right["name"].clone();
    let bytes = serde_json::to_vec(&artifact).unwrap();
    let mut lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.lock()).unwrap()).unwrap();
    lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
    lock["artifact_bytes"] = bytes.len().into();
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
    check_return_call_sidecar(
        &project,
        &import,
        r#"
        verifying "unused.cpp";
        int32 call(const struct Box__int& box) { ensures result == 7; }
        by { execute(); simp(); }
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
            "template<class T> struct Box { int value; }; int call(const Box<const int>& box) noexcept { return box.value; }",
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
        (
            "struct Box; int call(const Box& box) noexcept { return 7; }",
            "incomplete type",
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
    let lowered = lower_import(&import).unwrap();
    let boundaries: Vec<_> = lowered.record_layouts()["Envelope"]
        .records()
        .iter()
        .map(|record| {
            (
                record.name(),
                record.offset_bytes(),
                record.size_bytes(),
                record.parent(),
            )
        })
        .collect();
    assert_eq!(
        boundaries,
        vec![
            ("left", 0, 16, None),
            ("left.base", 0, 16, Some(0)),
            ("right", 16, 16, None),
            ("right.base", 16, 16, Some(2)),
        ]
    );
    fs::remove_file(&project.exporter).unwrap();
    check_return_call_sidecar(
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
        } by { execute(); simp(); }
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
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
            "int32 Deep_Observe(const struct Deep* this) { views this->base.base.size; ensures result == this->base.base.size; }",
        ),
        (
            "Envelope::Read",
            "int32 Envelope_Read(const struct Envelope* this) { views this->left.base.base.size; ensures result == this->left.base.base.size; }",
        ),
        (
            "Envelope::Copy",
            "void Envelope_Copy(struct Envelope* this) { views this->left.base.base.size; owns this->right.base.size; ensures this->right.base.size == this->left.base.base.size; ensures this->left.base.base.size == old(this->left.base.base.size); }",
        ),
    ] {
        let project = Project::with_fixture("inherited.cpp", selected, INHERITED_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar =
            format!("verifying \"inherited.cpp\"; {contract} by {{ execute(); simp(); }}");
        fs::remove_file(&project.exporter).unwrap();
        check_return_call_sidecar(&project, &import, &sidecar);
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn inherited_method_and_reference_calls_verify_offline_with_sibling_frames() {
    for (selected, sidecar) in [
        (
            "Envelope::Via",
            r#"
        int32 Base_Read(const struct Base* this) { views this->size; ensures result == this->size; } by { execute(); simp(); }
        int32 Envelope_Via(const struct Envelope* this) { views this->left.base.base.size; views this->right.base.size; ensures result == this->left.base.base.size; ensures this->right.base.size == old(this->right.base.size); } by { execute(); simp(); }
        "#,
        ),
        (
            "Envelope::Write",
            r#"
        void Base_Set(struct Base* this, int32 next) { owns this->size; ensures this->size == next; } by { execute(); simp(); }
        void Envelope_Write(struct Envelope* this, int32 next) { owns this->right.base.size; views this->left.base.base.size; ensures this->right.base.size == next; ensures this->left.base.base.size == old(this->left.base.base.size); } by { execute(); simp(); }
        "#,
        ),
        (
            "call",
            r#"
        int32 Helper(const struct Base& value) { views value.size; ensures result == value.size; } by { execute(); simp(); }
        int32 call(const struct Envelope& state) { views state.left.base.base.size; views state.unrelated.size; ensures result == state.left.base.base.size; ensures state.unrelated.size == old(state.unrelated.size); } by { execute(); simp(); }
        "#,
        ),
        (
            "change",
            r#"
        void SetHelper(struct Base& value, int32 next) { owns value.size; ensures value.size == next; } by { execute(); simp(); }
        void change(struct Envelope& state, int32 next) { owns state.right.base.size; views state.left.base.base.size; ensures state.right.base.size == next; ensures state.left.base.base.size == old(state.left.base.base.size); } by { execute(); simp(); }
        "#,
        ),
    ] {
        let project = Project::with_fixture("inherited.cpp", selected, INHERITED_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        check_return_call_sidecar(
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
            let place = &mut hostile["function"]["body"][0]["arguments"][0]["place"];
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
                    hostile["function"]["parameters"][0]["value_type"]["pointee"]["is_const"] =
                        true.into();
                }
                7 => {
                    path.push(path[last].clone());
                }
                _ => unreachable!(),
            }
            let bytes = serde_json::to_vec(&hostile).unwrap();
            let mut lock = original_lock.clone();
            lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
            lock["artifact_bytes"] = bytes.len().into();
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
fn inherited_calls_reject_missing_authority_and_false_frames() {
    let project = Project::with_fixture("inherited.cpp", "call", INHERITED_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let sidecar = r#"
        verifying "inherited.cpp";
        int32 Helper(const struct Base& value) { views value.size; ensures result == value.size; } by { execute(); simp(); }
        int32 call(const struct Envelope& state) { views state.left.base.base.size; views state.unrelated.size; ensures result == state.left.base.base.size; ensures state.unrelated.size == old(state.unrelated.size); } by { execute(); simp(); }
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
                "verifying \"conversion.cpp\"; int64 {selected}(uint64 value) {{ requires value == {value}u64; ensures result == {expected}i64; }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &source);
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
fn cpp20_signed_unsigned_round_trips_verify_without_input_bounds() {
    for (selected, value_type) in [
        ("signed_round_trip", "int64"),
        ("unsigned_round_trip", "uint64"),
    ] {
        let project = Project::with_fixture("conversion.cpp", selected, SIGNED_CONVERSION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"conversion.cpp\"; {value_type} {selected}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn cpp20_modular_conversion_contract_preserves_bits_and_frames_memory() {
    let project = Project::with_fixture("conversion.cpp", "relay", SIGNED_CONVERSION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "conversion.cpp";
int64 explicit_cast(uint64 value) { ensures ((uint64)result) == value; } by { execute(); simp(); }
int64 relay(uint64 value, int32* untouched) {
 owns untouched[0..1];
 ensures ((uint64)result) == value;
 ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, source);
}

#[test]
fn cpp20_conversion_keeps_following_signed_overflow_obligations() {
    let project = Project::with_fixture("conversion.cpp", "arithmetic", SIGNED_CONVERSION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"conversion.cpp\"; int64 arithmetic(uint64 value) { requires value == 18446744073709551615u64; ensures result == 0i64; } by { execute(); simp(); }",
    );
    let source = "verifying \"conversion.cpp\"; int64 arithmetic(uint64 value) { requires value == 9223372036854775807u64; ensures result == 0i64; } by { execute(); simp(); }";
    fs::write(project.directory.join("bad.click"), source).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), source).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.message().contains("overflow"), "{}", error.message());
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn cpp20_fee_fast_paths_preserve_the_signed_return_conversion() {
    for (fee, at_size, size) in [
        (0u64, 1u64, 3u64),
        (7, 2, 3),
        (8, 2, 4),
        (8589934591, 2147483647, 2147483647),
    ] {
        for (selected, instance, expected) in [
            ("fee_down", "fee__bool_true", (fee * at_size / size) as i64),
            (
                "fee_up",
                "fee__bool_false",
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
                "verifying \"conversion.cpp\"; int64 {instance}(int64 fee, int32 at_size, int32 size) {{ {contract} }} by {{ execute(); simp(); }} int64 {selected}(int64 fee_value, int32 at_size, int32 size) {{ {caller_contract} }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &source);
        }
    }
}

const RETURN_CALL_SOURCE: &str = include_str!("fixtures/cpp-verification/return-call/relay.cpp");

#[test]
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
    ] = import.export().function.body.as_slice()
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
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(int32 value, int32* untouched) {
 owns untouched[0..1];
 ensures result == value;
 ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
}

#[test]
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
            "verifying \"relay.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {selected}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
    }
    let project = Project::with_fixture("relay.cpp", "choose", RETURN_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 choose(bool first, int32 value) {
 ensures first != 0 implies result == value;
 ensures first == 0 implies result == 7;
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
}

#[test]
fn direct_return_calls_keep_internal_capture_names_fresh_and_reject_false_results() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "int echo(int value) noexcept { return value; } int relay(int __click_cpp_return_value) noexcept { return echo(__click_cpp_return_value); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(int32 __click_cpp_return_value) { ensures result == __click_cpp_return_value; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace("result == __click_cpp_return_value", "result == 7");
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn direct_return_calls_preserve_fee_method_template_wrappers() {
    for (selected, instance, expected) in [
        (
            "FeeFrac::EvaluateFeeDown",
            "FeeFrac_EvaluateFee__bool_true",
            4i64,
        ),
        (
            "FeeFrac::EvaluateFeeUp",
            "FeeFrac_EvaluateFee__bool_false",
            5i64,
        ),
    ] {
        let project = Project::with_fixture("relay.cpp", selected, RETURN_CALL_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof_name = selected.replace("::", "_");
        let contract = format!(
            "views this->fee; views this->size; requires this->fee == 7i64; requires this->size == 3; requires at_size == 2; ensures result == {expected}i64; ensures this->fee == old(this->fee); ensures this->size == old(this->size);"
        );
        let source = format!(
            "verifying \"relay.cpp\"; int64 {instance}(const struct FeeFrac* this, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }} int64 {proof_name}(const struct FeeFrac* this, int32 at_size) {{ {contract} }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
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
            "int echo(int value) noexcept; int relay(int value) noexcept { return echo(value); }",
            "no reachable function definition",
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
#[ignore = "nightly: 7s in the parallel gate"]
fn direct_return_calls_capture_typed_results_before_destructors() {
    check_return_cleanup_cases("int32");
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn direct_return_calls_capture_boolean_results_before_destructors() {
    check_return_cleanup_cases("bool");
}

#[test]
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
            "owns slot[0..1]; requires slot[0] == 7; ensures result == 1; ensures slot[0] == old(slot[0]);",
            "1",
        ),
        ("ordinary_wide", "", "int64", "", "", "4294967303i64"),
        ("ordinary_bool", "", "bool", "", "", "1"),
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
            format!(
                "{value_type} {helper}({helper_parameters}) {{ {helper_contract} }} by {{ execute(); simp(); }}"
            )
        };
        let nested_helper = if selected == "capture_nested" {
            "int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }"
        } else {
            ""
        };
        let source = format!(
            r#"verifying "cleanup.cpp";
void Restore_constructor(struct Restore* this, int32* slot) {{
 owns this->p; owns this->saved; owns slot[0..1];
 ensures this->p == slot; ensures this->saved == old(slot[0]); ensures slot[0] == 7;
 ensures separate(memory(*this), memory(this->p[0..1]));
}} by {{ execute(); simp(); }}
void Restore_destructor(struct Restore* this) {{
 requires separate(memory(*this), memory(this->p[0..1]));
 owns this->p; owns this->saved; owns this->p[0..1];
 ensures this->p == old(this->p); ensures this->saved == old(this->saved);
 ensures this->p[0] == old(this->saved);
}} by {{ execute(); simp(); }}
{helper_definition}
{nested_helper}
{value_type} {selected}(int32& value) {{
 owns value; ensures result == {expected}; ensures value == old(value);
}} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace(
            &format!("ensures result == {expected}; ensures value =="),
            "ensures result == 0; ensures value ==",
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

    // Uncaught cleanup edges are checked structurally: resource-bearing
    // exceptional contracts remain outside the existing surface slice.
    let escaping = Project::with_fixture("unwind.cpp", "escaping", cpp);
    escaping.write_exception_enabled_compilation_database();
    escaping.write_config_with_exception_behavior("escaping", "unwind.cpp", true, "scalar_int32");
    refresh_import(&escaping.config()).unwrap();
    let lowered = lower_import(&load_import(&escaping.config()).unwrap()).unwrap();
    fn has_unwind_cleanup(statement: &CStatement) -> bool {
        match statement {
            CStatement::TryCatchInt32 {
                handler,
                cleanup_unwind: true,
                ..
            } => {
                matches!(handler.as_ref(), CStatement::Seq(cleanup, rethrow) if contains_call(cleanup, "Restore_destructor") && matches!(rethrow.as_ref(), CStatement::Throw(_)))
            }
            CStatement::Seq(first, second) => {
                has_unwind_cleanup(first) || has_unwind_cleanup(second)
            }
            _ => false,
        }
    }
    assert!(has_unwind_cleanup(lowered.kernel_function().body()));
}

#[test]
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
int32 helper(bool should_throw) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 relay(bool should_throw) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace(
        "exceptional ensures exception == 7 by",
        "exceptional ensures exception == 8 by",
    );
    fs::write(project.directory.join("bad.click"), &hostile).unwrap();
    let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

#[test]
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
        let [CppStatement::ReturnCall { arguments, .. }] = import.export().function.body.as_slice()
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
        assert_eq!(capture_type, &import.export().function.return_type);
        let source = format!(
            "verifying \"nested.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {selected}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
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
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 collision(int32 __click_cpp_nested_value_0, int32 __click_cpp_nested_value_1) {
 ensures result == __click_cpp_nested_value_0;
} by { execute(); simp(); }
"#,
    );
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
fn nested_return_calls_propagate_inner_exceptions_without_evaluating_outer_call() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int value) { return value; } int relay(bool fail) { return outer(inner(fail)); }";
    let project = Project::with_fixture("nested.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "nested.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 inner(bool fail) throws int32 {
 ensures result == 5 by { execute(); simp(); }
 exceptional ensures exception == 7 by { execute(); simp(); }
}
int32 outer(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(bool fail) throws int32 {
 ensures result == 5 by { execute(); simp(); }
 exceptional ensures exception == 7 by { execute(); simp(); }
}
"#,
    );
}

#[test]
fn nested_return_calls_use_distinct_capture_types_across_branches() {
    let project = Project::with_fixture(
        "nested.cpp",
        "choose",
        include_str!("fixtures/cpp-verification/return-call/nested.cpp"),
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "nested.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int64 echo64(int64 value) { ensures result == value; } by { execute(); simp(); }
int64 outer32(int32 value) { requires value == 7; ensures result == 7i64; } by { execute(); simp(); }
int64 choose(bool first, int32 value) { requires value == 7; ensures result == 7i64; } by { execute(); simp(); }
"#,
    );
}

#[test]
fn nested_capture_name_probes_scale_with_calls_and_source_collisions() {
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
        // units; name probing must still grow linearly across all sizes.
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
            "verifying \"arguments.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }} int32 {outer}(int32 a, int32 b, int32 c) {{ ensures result == {slot}; }} by {{ execute(); simp(); }} int32 {selected}(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let [CppStatement::ReturnCall { arguments, .. }] = import.export().function.body.as_slice()
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
            "verifying \"arguments.cpp\"; {value_type} {inner}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {outer}({value_type} left, {value_type} right) {{ ensures result == right; }} by {{ execute(); simp(); }} {value_type} {selected}({value_type} value, int32 other) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
    }
}

#[test]
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
        let down = i32::from(round_down);
        let source = format!(
            r#"verifying "arguments.cpp";
int64 Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }} by {{ execute(); simp(); }}
int64 Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 EvaluateFee(int64 fee, int32 at_size, int32 divisor, bool round_down) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
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
fn nested_calls_with_stable_siblings_propagate_inner_exceptions() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int left, int value, bool flag) { return value; } int relay(bool fail, int left) { return outer(left, inner(fail), fail); }";
    let project = Project::with_fixture("arguments.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "arguments.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 inner(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 outer(int32 left, int32 value, bool flag) { ensures result == value; } by { execute(); simp(); }
int32 relay(bool fail, int32 left) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#,
    );
}

#[test]
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
fn stable_siblings_remain_valid_when_the_nested_call_writes_memory() {
    let project = Project::with_fixture(
        "arguments.cpp",
        "effectful_inner",
        MULTIPLE_ARGUMENTS_SOURCE,
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 write_seven(int32* slot) {
 owns slot[0..1]; ensures slot[0] == 7; ensures result == 7;
} by { execute(); simp(); }
int32 second(int32 a, int32 b, int32 c) { ensures result == b; } by { execute(); simp(); }
int32 effectful_inner(int32* slot, int32 snapshot) {
 owns slot[0..1]; ensures slot[0] == 7; ensures result == 7;
} by { execute(); simp(); }
"#,
    );
}

#[test]
fn fee_pattern_contracts_reject_zero_divisors_and_unproved_product_bounds() {
    for (selected, source) in [
        (
            "Div",
            "verifying \"arguments.cpp\"; int64 Div(int64 n, int32 d, bool round_down) { requires n == 21i64; requires d == 0; ensures result == result; } by { execute(); simp(); }",
        ),
        (
            "Mul",
            "verifying \"arguments.cpp\"; int64 Mul(int64 fee, int32 at_size) { requires fee == 9223372036854775807i64; requires at_size == 3; ensures result == result; } by { execute(); simp(); }",
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
fn scalar_local_siblings_survive_nested_memory_effects() {
    let project =
        Project::with_fixture("arguments.cpp", "local_sibling", MULTIPLE_ARGUMENTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "arguments.cpp";
int32 write_seven(int32* slot) { owns slot[0..1]; ensures slot[0] == 7; ensures result == 7; } by { execute(); simp(); }
int32 first(int32 a, int32 b, int32 c) { ensures result == a; } by { execute(); simp(); }
int32 local_sibling(int32* slot, int32 value) { owns slot[0..1]; ensures slot[0] == 7; ensures result == value; } by { execute(); simp(); }
"#,
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn nested_stable_siblings_preserve_concrete_boolean_template_rounding_wrappers() {
    for (selected, down, fee, expected) in [
        ("fee_down", 1, 7, 4),
        ("fee_up", 0, 7, 5),
        ("fee_down", 1, -7, -5),
        ("fee_up", 0, -7, -4),
    ] {
        let project = Project::with_fixture("arguments.cpp", selected, MULTIPLE_ARGUMENTS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] = import.export().function.body.as_slice()
        else {
            panic!("retain template return call");
        };
        let instance = &callee.name;
        let product = fee * 3;
        let source = format!(
            r#"verifying "arguments.cpp";
int64 Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }} by {{ execute(); simp(); }}
int64 Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {instance}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {selected}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
    }
}

const STATIC_HELPERS_SOURCE: &str =
    include_str!("fixtures/cpp-verification/return-call/static-helpers.cpp");

#[test]
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
        assert!(matches!(&import.export().function.function_kind,
            CppFunctionKind::StaticMethod { record_name, record_declaration_id }
            if record_name == "Scalar" && !record_declaration_id.is_empty()));
        assert_eq!(import.export().function.parameters.len(), 1);
        assert!(import.export().records.is_empty());
        let source = format!(
            "verifying \"static.cpp\"; {value_type} Scalar_{member}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace("result == value", "result != value");
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
fn static_helpers_support_modular_nested_and_initializer_calls() {
    for selected in ["static_chain", "static_local"] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            r#"verifying "static.cpp";
int32 Scalar_echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
int32 Other_echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
int32 {selected}(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
"#
        );
        // The local caller reaches only Scalar_echo.
        let source = if selected == "static_local" {
            source.replace("int32 Other_echo(int32 value) { ensures result == value; } by { execute(); simp(); }\n", "")
        } else {
            source
        };
        check_return_call_sidecar(&project, &import, &source);
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn static_helpers_preserve_nested_fee_rounding_template_shape() {
    for (selected, down, fee, expected) in [
        ("static_fee_down", 1, 7, 4),
        ("static_fee_up", 0, 7, 5),
        ("static_fee_down", 1, -7, -5),
        ("static_fee_up", 0, -7, -4),
    ] {
        let project = Project::with_fixture("static.cpp", selected, STATIC_HELPERS_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] = import.export().function.body.as_slice()
        else {
            panic!("static template call");
        };
        let product = fee * 3;
        let instance = &callee.name;
        let source = format!(
            r#"verifying "static.cpp";
int64 FeeMath_Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }} by {{ execute(); simp(); }}
int64 FeeMath_Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == 5; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {instance}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {selected}(int64 fee, int32 at_size, int32 divisor) {{ requires fee == {fee}i64; requires at_size == 3; requires divisor == 5; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
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
            "unsupported expression",
        ),
        (
            "struct H { static int echo(int x) noexcept { return x; } }; int relay(int x) noexcept { return ((void)++x, H{}).echo(x); }",
            "relay",
            "unsupported expression",
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
fn static_helpers_propagate_scalar_exceptions_through_nested_calls() {
    let cpp = "struct H { static int inner(bool fail) { if (fail) { throw 7; } return 5; } static int outer(int value) { return value; } static int relay(bool fail) { return outer(inner(fail)); } };";
    let project = Project::with_fixture("static.cpp", "H::relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("H::relay", "static.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "static.cpp";
int32 H_inner(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 H_outer(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 H_relay(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#,
    );
}

#[test]
fn static_helpers_called_from_value_methods_preserve_field_authority() {
    let project = Project::with_fixture("static.cpp", "FeeValue::Evaluate", STATIC_HELPERS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "static.cpp";
int64 FeeMath_Mul(int64 fee, int32 at_size) { requires fee == 7i64; requires at_size == 3; ensures result == 21i64; } by { execute(); simp(); }
int64 FeeValue_Evaluate(const struct FeeValue* this, int32 at_size) {
 owns this->fee;
 requires this->fee == 7i64;
 requires at_size == 3;
 ensures result == 21i64;
 ensures this->fee == old(this->fee);
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
            "int64 FeeMath_Mul(int64 fee, int32 at_size) { ensures result == result; } by { execute(); simp(); }",
        ),
        (
            "FeeMath::Div",
            "int64 FeeMath_Div(int64 n, int32 d, bool round_down) { ensures result == result; } by { execute(); simp(); }",
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
fn normalized_scalar_calls_agree_across_returns_initializers_and_discarded_results() {
    for (selected, contract) in [
        (
            "direct",
            "int32 direct(int32 value, int32 sibling) { ensures result == value; } by { execute(); simp(); }",
        ),
        (
            "initialized",
            "int32 initialized(int32 value, int32 sibling) { ensures result == value; } by { execute(); simp(); }",
        ),
        (
            "discarded",
            "int32 discarded(int32 value) { ensures result == value; } by { execute(); simp(); }",
        ),
    ] {
        let project =
            Project::with_fixture("evaluation.cpp", selected, NORMALIZED_EVALUATION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let helpers = if selected == "discarded" {
            ""
        } else {
            "int32 first(int32 value, int32 sibling) { ensures result == value; } by { execute(); simp(); }"
        };
        let source = format!(
            "verifying \"evaluation.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }} {helpers} {contract}"
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace("ensures result == value", "ensures result != value");
        fs::write(project.directory.join("bad.click"), &hostile).unwrap();
        let parsed = read_click_project(&project.directory.join("bad.click"), &hostile).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn normalized_initializer_calls_preserve_scalar_types_and_static_helpers() {
    for (selected, helper, value_type) in [
        ("initialized64", "echo64", "int64"),
        ("initialized_u32", "echo_u32", "uint32"),
        ("initialized_u64", "echo_u64", "uint64"),
        ("Helper::initialized", "Helper_echo", "int32"),
    ] {
        let project =
            Project::with_fixture("evaluation.cpp", selected, NORMALIZED_EVALUATION_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let caller = &import.export().function.name;
        let source = format!(
            "verifying \"evaluation.cpp\"; {value_type} {helper}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }} {value_type} {caller}({value_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &source);
    }
}

#[test]
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
void Restore_constructor(struct Restore* this, int32* value) {
 owns this->slot; owns this->saved; owns value[0..1];
 ensures this->slot == value;
 ensures this->saved == old(value[0]);
 ensures value[0] == 7;
 ensures separate(memory(*this), memory(this->slot[0..1]));
} by { execute(); simp(); }
void Restore_destructor(struct Restore* this) {
 requires separate(memory(*this), memory(this->slot[0..1]));
 owns this->slot; owns this->saved; owns this->slot[0..1];
 ensures this->slot == old(this->slot);
 ensures this->saved == old(this->saved);
 ensures this->slot[0] == old(this->saved);
} by { execute(); simp(); }
int32 read(int32* slot) { owns slot[0..1]; ensures result == old(slot[0]); ensures slot[0] == old(slot[0]); } by { execute(); simp(); }
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 initialized_cleanup(int32& value) { owns value; ensures result == 7; ensures value == old(value); } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
            .get("guard")
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
fn normalized_initializer_calls_propagate_inner_exceptions() {
    let cpp = "int inner(bool fail) { if (fail) { throw 7; } return 5; } int outer(int value) { return value; } int relay(bool fail) { int captured = outer(inner(fail)); return captured; }";
    let project = Project::with_fixture("evaluation.cpp", "relay", cpp);
    project.write_exception_enabled_compilation_database();
    project.write_config_with_exception_behavior("relay", "evaluation.cpp", true, "scalar_int32");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "evaluation.cpp";
int32 inner(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 outer(int32 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#,
    );
}

#[test]
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
    ] = import.export().function.body.as_slice()
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
    check_return_call_sidecar(&project, &import, &source);
    let false_claim = source.replace(
        "early != 0 implies result == 7",
        "early != 0 implies result == 9",
    );
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, &false_claim).unwrap();
    let false_project = read_click_project(&sidecar, &false_claim).unwrap();
    verify_program_prepared_project(&false_project, &import)
        .expect_err("a future object cannot change the early return result");
}

#[test]
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
    ] = import.export().function.body.as_slice()
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
            "early != 0 implies result == 7",
            "early != 0 implies result == old(value)",
        )
        .replace(
            "early == 0 implies result == 9",
            "early == 0 implies result == 7",
        );
    check_return_call_sidecar(&project, &import, &source);
}

#[test]
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
        sidecar.push_str(&format!("int32 {name}({parameter_type} x) {{ ensures result == {value}; }} by {{ execute(); simp(); }}\n"));
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
    sidecar.push_str("int32 relay(int64 x, int64 y, int32 z) { ensures result == 76; } by { execute(); simp(); }\n");
    check_return_call_sidecar(&project, &import, &sidecar);
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
    assert_eq!(lowered.kernel_function().name(), "A_Nested_echo");
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"namespace.cpp\"; int32 A_Nested_echo(int32 x) { ensures result == x; } by { execute(); simp(); }",
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
        .contract_name(&import.export().function.declaration_id)
        .unwrap();
    let helper = lowered
        .contract_name(&import.export().reachable_functions[0].declaration_id)
        .unwrap();
    assert_ne!(selected, helper);
    assert_eq!(lowered.kernel_function().name(), selected);
    let sidecar = format!(
        "verifying \"selected.cpp\"; int32 {helper}(int32 x) {{ ensures result == 5; }} by {{ execute(); simp(); }} int32 {selected}(int32 x) {{ ensures result == 5; }} by {{ execute(); simp(); }}"
    );
    check_sidecar_tactic(&project, &import, &sidecar, Some(&format!("{selected}.")));
}

#[test]
fn anonymous_namespace_helper_has_a_valid_identity_based_contract_name() {
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
    assert!(name.starts_with("__click_cpp_decl_"));
    let sidecar = format!(
        "verifying \"anonymous.cpp\"; int32 {name}(int32 x) {{ ensures result == x; }} by {{ execute(); simp(); }} int32 relay(int32 x) {{ ensures result == x; }} by {{ execute(); simp(); }}"
    );
    check_return_call_sidecar(&project, &import, &sidecar);
}

#[test]
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
            "verifying \"forest.cpp\"; int64 total() { ensures result == 4i64; } by { execute(); simp(); }",
        );
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn record_inventories_and_function_lowering_share_indexes_across_sizes() {
    for size in [2usize, 8, 32, 128] {
        let mut cpp = String::new();
        let mut sidecar = String::from("verifying \"records.cpp\";\n");
        for index in 0..size {
            cpp.push_str(&format!("struct R{index} {{ int value; }}; int read{index}(int x) noexcept {{ R{index} local{{x}}; return local.value; }}\n"));
            sidecar.push_str(&format!("int32 read{index}(int32 x) {{ ensures result == x; }} by {{ execute(); simp(); }}\n"));
        }
        cpp.push_str("int relay(int x) noexcept {\n");
        for index in 0..size {
            cpp.push_str(&format!("int y{index} = read{index}(x);\n"));
        }
        cpp.push_str(&format!("return y{}; }}\n", size - 1));
        sidecar
            .push_str("int32 relay(int32 x) { ensures result == x; } by { execute(); simp(); }\n");
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
            check_return_call_sidecar(&project, &import, &sidecar);
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
    let sidecar = "verifying \"layouts.cpp\"; int64 choose(struct First& first, struct Second& second) { owns first.value; owns second.value; ensures first.value == 7; ensures result == old(second.value); ensures second.value == old(second.value); } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, sidecar);
    let missing_authority = sidecar.replace("owns second.value;", "");
    let path = project.directory.join("wrong.click");
    fs::write(&path, &missing_authority).unwrap();
    let parsed = read_click_project(&path, &missing_authority).unwrap();
    assert!(verify_program_prepared_project(&parsed, &import).is_err());
}

const GROWING_GUARD_SOURCE: &str = "struct Guard { int value; explicit Guard(int initial) noexcept : value(initial) {} ~Guard() noexcept { value = 0; } };\n";

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn growing_lifetime_inventories_keep_prefix_returns_and_reverse_cleanup() {
    check_growing_lifetime_inventory("top");
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn growing_sibling_lifetime_inventories_keep_prefix_returns_and_reverse_cleanup() {
    check_growing_lifetime_inventory("siblings");
}

#[test]
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
        let bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
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
        let order = destructor_object_order(lowered.kernel_function().body(), "Guard_destructor");
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
void Guard_constructor(struct Guard* this, int32 initial) { owns this->value; ensures this->value == initial; } by { execute(); simp(); }
void Guard_destructor(struct Guard* this) { owns this->value; ensures this->value == 0; } by { execute(); simp(); }
int32 many(bool early, int32 value) { ensures result == value; } by { execute(); simp(); }
"#;
            check_return_call_sidecar(&project, &import, source);
            let hostile = source.replace(
                "ensures result == value; } by { execute(); simp(); }",
                "requires value == 5; ensures result == 6; } by { execute(); assumption(); }",
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
            "n == 1",
            "1i64",
        ),
        (
            "unsigned convert(bool n) noexcept { return static_cast<unsigned>(n); }",
            "uint32 convert(bool n)",
            "n == 0",
            "0u32",
        ),
    ] {
        let project = Project::with_fixture("scalar.cpp", "convert", cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let proof = format!(
            "verifying \"scalar.cpp\"; {signature} {{ requires {precondition}; ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &proof);
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
fn compiler_assumptions_require_proof_and_keep_normal_cleanup() {
    let cpp = "struct Guard { int value; explicit Guard(int n) noexcept : value(n) {} ~Guard() noexcept { value = 0; } };\nint guarded(int n) noexcept { Guard guard(n); __builtin_assume(n > 0); return n; }";
    let project = Project::with_fixture("assume.cpp", "guarded", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().function.body[1],
        CppStatement::Assume { .. }
    ));
    let contracts = r#"verifying "assume.cpp";
void Guard_constructor(struct Guard* this, int32 n) { owns this->value; ensures this->value == n; } by { execute(); simp(); }
void Guard_destructor(struct Guard* this) { owns this->value; ensures this->value == 0; } by { execute(); simp(); }
"#;
    let source = format!(
        "{contracts}\nint32 guarded(int32 n) {{ requires n > 0; ensures result == n; }} by {{ execute(); simp(); }}"
    );
    check_return_call_sidecar(&project, &import, &source);
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
fn compiler_assumptions_cover_total_predicates_and_scale_with_statements() {
    for size in [4usize, 16, 64, 256] {
        let body = "__builtin_assume(n > 0 && bool(n));\n".repeat(size);
        let cpp = format!("int guarded(int n) noexcept {{ {body} return n; }}");
        let project = Project::with_fixture("assume.cpp", "guarded", &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
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
            let proof = "verifying \"assume.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }";
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
fn user_named_assume_calls_are_not_compiler_assumptions() {
    let cpp = "void Assume(bool condition) noexcept { int ignored = 0; }\nint guarded(int n) noexcept { Assume(n > 0); return n; }";
    let project = Project::with_fixture("assume.cpp", "guarded", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().function.body[0],
        CppStatement::Call { .. }
    ));
    let proof = "verifying \"assume.cpp\"; void Assume(bool condition) { ensures condition == condition; } by { execute(); simp(); } int32 guarded(int32 n) { ensures result == n; } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, proof);
    let hostile = proof.replace("ensures result == n;", "ensures n > 0;");
    let path = project.directory.join("false.click");
    fs::write(&path, &hostile).unwrap();
    let parsed = read_click_project(&path, &hostile).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .expect_err("a library spelling cannot introduce a compiler assumption");
}

#[test]
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
            "verifying \"assume.cpp\"; int32 guarded(int32 n) {{ {requires} ensures result == n; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &proof);
    }
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn isolated_nested_calls_snapshot_field_siblings_in_every_scalar_context() {
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
            "verifying \"fields.cpp\"; int32 echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }} int32 {outer}(int32 a, int32 b, int32 c) {{ ensures result == {slot}; }} by {{ execute(); simp(); }} int32 {selected}(const struct Box& box) {{ owns box.value; owns box.other; {requires} ensures result == {claim}; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &proof);
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
                .expect_err("field snapshots need authority and cannot prove false results");
        }
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn field_siblings_preserve_fee_template_rounding_and_static_helper_shape() {
    check_field_sibling_rounding("Down");
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn field_siblings_preserve_upward_fee_template_rounding_and_static_helper_shape() {
    check_field_sibling_rounding("Up");
}

fn check_field_sibling_rounding(direction: &str) {
    let cpp = include_str!("fixtures/cpp-verification/return-call/field-fee-rounding.cpp");
    for (selected, down, fee, divisor, expected) in [
        ("Down", 1, 7, 5, 4),
        ("Up", 0, 7, 5, 5),
        ("Down", 1, -7, 5, -5),
        ("Up", 0, -7, 5, -4),
        ("Down", 1, 7, 3, 7),
        ("Up", 0, -7, 3, -7),
    ] {
        if selected != direction {
            continue;
        }
        let project = Project::with_fixture("fields.cpp", &format!("Fee::{selected}"), cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let [CppStatement::ReturnCall { callee, .. }] = import.export().function.body.as_slice()
        else {
            panic!("retain method template call");
        };
        let instance = &callee.name;
        let product = fee * 3;
        let proof = format!(
            r#"verifying "fields.cpp";
int64 Fee_Mul(int64 fee, int32 at_size) {{ requires fee == {fee}i64; requires at_size == 3; ensures result == {product}i64; }} by {{ execute(); simp(); }}
int64 Fee_Div(int64 n, int32 d, bool round_down) {{ requires n == {product}i64; requires d == {divisor}; requires round_down == {down}; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 {instance}(const struct Fee* this, int32 at_size) {{ owns this->fee; owns this->size; requires this->fee == {fee}i64; requires this->size == {divisor}; requires at_size == 3; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
int64 Fee_{selected}(const struct Fee* this, int32 at_size) {{ owns this->fee; owns this->size; requires this->fee == {fee}i64; requires this->size == {divisor}; requires at_size == 3; ensures result == {expected}i64; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &proof);
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
int32 inner(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int32 outer(int32 a, int32 b) { ensures result == b; } by { execute(); simp(); }
int32 relay(bool fail, const struct Box& box) throws int32 {
 requires fail == true;
 ensures result == result by { execute(); simp(); }
 exceptional ensures exception == 7 by { execute(); simp(); }
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
        let bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
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
            "requires a == 4294967296i64; requires b == 4294967296i64; ensures result == 1;",
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
        let source = format!(
            "verifying \"wide.cpp\"; {result_type} {name}({params}) {{ {contract} }} by {{ execute(); simp(); }}"
        );
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
        let source = format!(
            "verifying \"wide.cpp\"; {return_type} {name}({params}) {{ {contract} }} by {{ execute(); simp(); }}"
        );
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
            "1",
            "170141183460469231731687303715884105727",
        ),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_INTERMEDIATES_SOURCE);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        let artifact = serde_json::to_value(import.export()).unwrap();
        let initializer = &artifact["function"]["body"][0]["initializer"]["value"];
        assert_eq!(initializer["kind"], "compiler_constant");
        assert_eq!(initializer["value"], payload);
        assert_eq!(initializer["value_type"]["bits"], 128);
        let source = format!(
            "verifying \"wide.cpp\"; {result_type} {name}() {{ ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn wide_intermediates_modular_calls_preserve_cast_round_trips() {
    let project = Project::with_fixture("wide.cpp", "relay", WIDE_INTERMEDIATES_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "wide.cpp";
int64 signed_round_trip(int64 value) { ensures result == value; } by { execute(); simp(); }
int64 relay(int64 value) { ensures result == value; } by { execute(); simp(); }
"#,
    );
}

#[test]
fn wide_intermediates_reject_false_high_bit_and_narrowing_claims() {
    for (name, return_type, expected) in [
        ("product_truth", "bool", "0"),
        ("product_low", "uint64", "1u64"),
    ] {
        let project = Project::with_fixture("wide.cpp", name, WIDE_INTERMEDIATES_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"wide.cpp\"; {return_type} {name}(int64 a, int64 b) {{ requires a == 4294967296i64; requires b == 4294967296i64; ensures result == {expected}; }} by {{ execute(); simp(); }}"
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
        let source = format!(
            "verifying \"wide.cpp\"; {ty} {name}({params}) {{ {contract} }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn wide_contracts_compose_modular_calls_and_frame_narrow_memory() {
    let project = Project::with_fixture("wide.cpp", "relay", WIDE_CONTRACTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "wide.cpp";
int128 identity(int128 value) { ensures to_integer(result) == to_integer(value); } by { execute(); simp(); }
int128 relay(int128 value, int32& untouched) {
    owns untouched;
    ensures to_integer(result) == to_integer(value);
    ensures untouched == old(untouched);
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
}

#[test]
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
            "verifying \"wide.cpp\"; {ty} {name}({ty} value) {{ requires to_integer(value) == {value}; ensures to_integer(result) == 0; }} by {{ execute(); simp(); }}"
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
            "verifying \"wide.cpp\"; {signature} {{ ensures to_integer(result) == to_integer(result); }} by {{ execute(); simp(); }}"
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
fn wide_contracts_nested_calls_report_pending_observer_chains() {
    let project = Project::with_fixture("wide.cpp", "nested", WIDE_CONTRACTS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "wide.cpp";
int128 identity(int128 value) { ensures to_integer(result) == to_integer(value); } by { execute(); simp(); }
int128 nested(int128 value) { ensures to_integer(result) == to_integer(result); } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, proof);
    // Bounded simp recognizes exact Integer equalities, not equality chains.
    let stronger = proof.replace(
        "int128 nested(int128 value) { ensures to_integer(result) == to_integer(result); }",
        "int128 nested(int128 value) { ensures to_integer(result) == to_integer(value); }",
    );
    let sidecar = project.directory.join("nested.click");
    fs::write(&sidecar, &stronger).unwrap();
    let parsed = read_click_project(&sidecar, &stronger).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(
        error.message().contains("unclosed goal"),
        "{}",
        error.message()
    );
}

#[test]
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
            "verifying \"wide.cpp\"; int128 select({params}) {{ ensures to_integer(result) == to_integer(p0); }} by {{ execute(); simp(); }}"
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
        assert_eq!(import.export().schema, 60);
        let source = format!(
            "verifying \"wide.cpp\"; {ty} {name}({ty} a, {ty} b) {{ {domain} ensures to_integer(result) == {helper}(to_integer(a), to_integer(b)); }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
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
                check_arithmetic_sidecar(&project, &import, &specialized);
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
            "verifying \"wide.cpp\"; {ty} {name}() {{ ensures to_integer(result) == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
    }
}

#[test]
fn wide_division_modular_calls_frame_narrow_memory() {
    let project = Project::with_fixture("wide.cpp", "signed_relay", WIDE_DIVISION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = format!(
        r#"verifying "wide.cpp";
int128 signed_quotient(int128 a, int128 b) {{
    {WIDE_SIGNED_DOMAIN}
    ensures to_integer(result) == truncating_quotient(to_integer(a), to_integer(b));
}} by {{ execute(); simp(); }}
int128 signed_relay(int128 a, int128 b, int32* untouched) {{
    {WIDE_SIGNED_DOMAIN}
    owns untouched[0..1];
    ensures to_integer(result) == truncating_quotient(to_integer(a), to_integer(b));
    ensures untouched[0] == old(untouched[0]);
}} by {{ execute(); simp(); }}
"#
    );
    check_return_call_sidecar(&project, &import, &source);
}

#[test]
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
        ] = import.export().function.body.as_slice()
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
                "verifying \"wide.cpp\"; int128 narrow_divisor(int128 a, int64 b) {{ {WIDE_SIGNED_DOMAIN} ensures to_integer(result) == truncating_quotient(to_integer(a), to_integer(b)); }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &proof);
        }
    }
    let project = Project::with_fixture("wide.cpp", "mixed_constant", WIDE_DIVISION_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"wide.cpp\"; uint128 mixed_constant() { ensures to_integer(result) == 113427455640312821154458202477256070485; } by { execute(); simp(); }",
    );
}

#[test]
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
            "verifying \"wide.cpp\"; {ty} {name}({ty} a, {ty} b) {{ {domain} ensures 0 == 0; }} by {{ execute(); simp(); }}"
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
            assert_eq!(import.export().schema, 60);
            let relation = format!("to_integer(a) {op} to_integer(b)");
            let proof = format!(
                "verifying \"wide.cpp\"; bool {name}({ty} a, {ty} b) {{ ensures result == 1 implies ({relation}); ensures result == 0 implies not ({relation}); }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &proof);
            let false_proof = proof.replace(
                "ensures result == 0 implies not",
                "ensures result == 0 implies",
            );
            let path = project.directory.join("false.click");
            fs::write(&path, &false_proof).unwrap();
            let parsed = read_click_project(&path, &false_proof).unwrap();
            assert!(verify_program_prepared_project(&parsed, &import).is_err());
        }
    }
}

#[test]
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
        let expected = u32::from(expected);
        let proof = format!(
            "verifying \"wide.cpp\"; bool {name}() {{ ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &proof);
        let false_proof = proof.replace(&format!("== {expected}"), &format!("== {}", 1 - expected));
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
        "verifying \"wide.cpp\"; bool narrow_compare(int128 a, int64 b) { ensures result == 1 implies to_integer(a) < to_integer(b); ensures result == 0 implies not (to_integer(a) < to_integer(b)); } by { execute(); simp(); }",
    );
}

#[test]
fn wide_comparisons_control_branches_and_frame_modular_call_memory() {
    let project = Project::with_fixture("wide.cpp", "choose", WIDE_COMPARISONS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"wide.cpp\"; int32 choose(int128 a, int128 b) { ensures to_integer(a) < to_integer(b) implies result == 7; ensures not (to_integer(a) < to_integer(b)) implies result == 11; } by { execute(); simp(); }";
    check_arithmetic_sidecar(&project, &import, proof);
    let project = Project::with_fixture("wide.cpp", "relay", WIDE_COMPARISONS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "wide.cpp";
bool signed_less(int128 a, int128 b) {
    requires to_integer(a) < to_integer(b);
    ensures result == 1;
} by { execute(); simp(); }
bool relay(int128 a, int128 b, int32* untouched) {
    requires to_integer(a) < to_integer(b);
    owns untouched[0..1];
    ensures result == 1;
    ensures untouched[0] == old(untouched[0]);
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, proof);
}

#[test]
fn wide_comparisons_do_not_erase_operand_division_guards() {
    let project = Project::with_fixture("wide.cpp", "unsafe_operand", WIDE_COMPARISONS_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    for domain in ["", "requires to_integer(b) != 0;"] {
        let proof = format!(
            "verifying \"wide.cpp\"; bool unsafe_operand(int128 a, int128 b) {{ {domain} ensures 0 == 0; }} by {{ execute(); simp(); }}"
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
                "verifying \"wide.cpp\"; bool {name}({ty} a, {ty} b) {{ requires to_integer(a) {inverse} to_integer(b); ensures result == 0; }} by {{ execute(); simp(); }}"
            );
            check_arithmetic_sidecar(&project, &import, &proof);
        }
    }
}

#[test]
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
            "verifying \"comparison.cpp\"; bool unequal({ty} a, {ty} b) {{ ensures result == 1 implies a != b; ensures result == 0 implies a == b; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &proof);
    }
}

const WIDE_NARROWING_SOURCE: &str =
    include_str!("fixtures/cpp-verification/wide-narrowing/narrow.cpp");

fn cast_identity_certificate(original: &str, lo: &str, hi: &str) -> String {
    format!(
        r#"arithmetic_certificate rules {{
        premise 0: {lo} <= {original} => {lo} <= {original};
        premise 1: {original} <= {hi} => {original} <= {hi};
        integer_cast_identity bounds [0, 1] => to_integer(result) == {original};
        conclusion 0;
    }}"#
    )
}

#[test]
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
        let cert = cast_identity_certificate("to_integer(a)", lo, hi);
        let proof = format!(
            "verifying \"narrow.cpp\"; {result} {name}({source} a) {{ requires {lo} <= to_integer(a); requires to_integer(a) <= {hi}; ensures to_integer(result) == to_integer(a); }} by {{ execute(); have to_integer(result) == to_integer(a) by {{ {cert} }} simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &proof);
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
        let cert = cast_identity_certificate(&observed, lo, hi);
        let proof = format!(
            "verifying \"narrow.cpp\"; {result} {name}(int128 a, int128 b) {{ requires to_integer(b) != 0; requires to_integer(a) != -170141183460469231731687303715884105728 or to_integer(b) != -1; requires {lo} <= {observed}; requires {observed} <= {hi}; ensures to_integer(result) == {observed}; }} by {{ execute(); have to_integer(result) == {observed} by {{ {cert} }} simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &proof);
        let unsafe_proof = format!(
            "verifying \"narrow.cpp\"; {result} {name}(int128 a, int128 b) {{ ensures 0 == 0; }} by {{ execute(); simp(); }}"
        );
        let path = project.directory.join("unsafe.click");
        fs::write(&path, &unsafe_proof).unwrap();
        let parsed = read_click_project(&path, &unsafe_proof).unwrap();
        let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
        assert!(
            error.message().contains("undefined behavior"),
            "{}",
            error.message()
        );
    }
}

#[test]
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
            "verifying \"narrow.cpp\"; {ty} {name}() {{ ensures to_integer(result) == {expected}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &proof);
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
fn wide_narrowing_modular_contract_preserves_framed_narrow_memory() {
    let project = Project::with_fixture("narrow.cpp", "relay", WIDE_NARROWING_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lo = "-9223372036854775808";
    let hi = "9223372036854775807";
    let cert = cast_identity_certificate("to_integer(a)", lo, hi);
    let proof = format!(
        r#"verifying "narrow.cpp";
int64 ss64(int128 a) {{
    requires {lo} <= to_integer(a);
    requires to_integer(a) <= {hi};
    ensures to_integer(result) == to_integer(a);
}} by {{ execute(); have to_integer(result) == to_integer(a) by {{ {cert} }} simp(); }}
int64 relay(int128 a, int32* untouched) {{
    requires {lo} <= to_integer(a);
    requires to_integer(a) <= {hi};
    owns untouched[0..1];
    ensures to_integer(result) == to_integer(a);
    ensures untouched[0] == old(untouched[0]);
}} by {{ execute(); simp(); }}"#
    );
    check_return_call_sidecar(&project, &import, &proof);
}

const SCALAR_BRACES_SOURCE: &str =
    include_str!("fixtures/cpp-verification/scalar-braces/braces.cpp");

#[test]
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
        ("truth", "bool", "", "result == 1"),
        ("constant", "int64", "", "result == 2147483648i64"),
    ] {
        let project = Project::with_fixture("braces.cpp", name, SCALAR_BRACES_SOURCE);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let source = format!(
            "verifying \"braces.cpp\"; {ty} {name}({params}) {{ ensures {post}; }} by {{ execute(); simp(); }}"
        );
        check_arithmetic_sidecar(&project, &import, &source);
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
            "using U32 = unsigned; int missing() noexcept; int refused({params}) noexcept {{ return {value}; }}"
        );
        let project = Project::with_fixture("braces.cpp", "refused", &cpp);
        refresh_import(&project.config())
            .expect_err("unsupported initialization must remain refused");
        assert!(!project.artifact().exists());
        assert!(!project.lock().exists());
    }
}

#[test]
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
}} by {{ execute(); simp(); }}
"#
    );
    check_return_call_sidecar(&project, &import, &source);
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
fn scalar_braces_keep_argument_and_assumption_effect_restrictions() {
    let project = Project::with_fixture("braces.cpp", "argument", SCALAR_BRACES_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"braces.cpp\"; int64 identity(int64 n) { ensures result == n; } by { execute(); simp(); } int64 argument(int32 n) { ensures result == n; } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, proof);
    let project = Project::with_fixture("braces.cpp", "guarded", SCALAR_BRACES_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"braces.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }";
    check_arithmetic_sidecar(&project, &import, proof);
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
    let CppStatement::LibraryAssert { contract, span, .. } = &import.export().function.body[1]
    else {
        panic!("explicit library assertion node")
    };
    assert_eq!(contract.function, "library::check");
    assert_eq!(contract.header, "gate.h");
    assert_eq!(span.file, "library.cpp");
    let source = r#"verifying "library.cpp";
void Guard_constructor(struct Guard* this, int32 n) { owns this->value; ensures this->value == n; } by { execute(); simp(); }
void Guard_destructor(struct Guard* this) { owns this->value; ensures this->value == 0; } by { execute(); simp(); }
int32 guarded(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
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
fn branch_likelihood_attributes_preserve_both_outcomes() {
    let cpp = "int choose(bool positive) noexcept { if (positive) [[likely]] { return 7; } else [[unlikely]] { return -3; } }";
    let project = Project::with_fixture("weights.cpp", "choose", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "weights.cpp";
int32 choose(bool positive) {
 ensures positive != 0 implies result == 7;
 ensures positive == 0 implies result == -3;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
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
                let bytes = serde_json::to_vec(&config).unwrap();
                lock["config_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
                fs::write(project.config(), bytes).unwrap();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
fn assumed_library_assertions_scale_with_explicit_statement_count() {
    for size in [4usize, 16, 64, 256] {
        let body = "library::check(n > 0);\n".repeat(size);
        let cpp =
            format!("#include \"gate.h\"\nint guarded(int n) noexcept {{ {body} return n; }}");
        let project = library_assertion_fixture(LIBRARY_ASSERTION_HEADER, &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
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
            let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }";
            check_return_call_sidecar(&project, &import, proof);
        }
    }
}

#[test]
fn assumed_library_assertions_compose_with_modular_callers_and_memory_framing() {
    let cpp = "#include \"gate.h\"\nint checked(int n) noexcept { library::check(n > 0); return n; }\nint guarded(int& memory, int n) noexcept { return checked(n); }";
    // A declaration-only, void-return library boundary is also explicitly assumed.
    let project = library_assertion_fixture("namespace library { void check(bool); }", cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "library.cpp";
int32 checked(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }
int32 guarded(int32& memory, int32 n) { owns memory; requires memory == 7; requires n > 0; ensures memory == 7; ensures result == n; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
fn consteval_library_metadata_keeps_proof_obligations_and_compiler_provenance() {
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let CppStatement::LibraryAssert {
        metadata,
        specialization,
        ..
    } = &import.export().function.body[0]
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
    let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, proof);
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
fn consteval_library_metadata_preserves_normal_cleanup_and_modular_framing() {
    let cpp = "#include \"gate.h\"\nstruct Guard { int value; explicit Guard(int n) noexcept : value(n) {} ~Guard() noexcept { value = 0; } };\nint checked(int n) noexcept { Gate(n > 0); return n; }\nint guarded(int& memory, int n) noexcept { Guard guard(n); return checked(n); }";
    let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, cpp);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "library.cpp";
void Guard_constructor(struct Guard* this, int32 n) { owns this->value; ensures this->value == n; } by { execute(); simp(); }
void Guard_destructor(struct Guard* this) { owns this->value; ensures this->value == 0; } by { execute(); simp(); }
int32 checked(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }
int32 guarded(int32& memory, int32 n) { owns memory; requires memory == 7; requires n > 0; ensures memory == 7; ensures result == n; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, proof);
}

#[test]
fn consteval_library_metadata_offline_checker_rejects_forged_provenance_and_kind() {
    use sha2::{Digest, Sha256};
    let cpp = "#include \"gate.h\"\nint guarded(int n) noexcept { Gate(n > 0); return n; }";
    for change in ["file", "function", "specialization", "too_many", "kind"] {
        let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, cpp);
        refresh_import(&project.config()).unwrap();
        let mut artifact: serde_json::Value =
            serde_json::from_slice(&fs::read(project.artifact()).unwrap()).unwrap();
        let statement = &mut artifact["function"]["body"][0];
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
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.contains("metadata"), "{error}");
    }
}

#[test]
fn consteval_library_metadata_scales_with_explicit_statement_count() {
    for size in [4usize, 16, 64, 256] {
        let body = "Gate(n > 0);\n".repeat(size);
        let cpp =
            format!("#include \"gate.h\"\nint guarded(int n) noexcept {{ {body} return n; }}");
        let project = consteval_library_fixture(CONSTEVAL_LIBRARY_HEADER, &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
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
        } = &import.export().function.body[0]
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
        let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }";
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
        let literal = &mut artifact["function"]["body"][0]["metadata"][1];
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
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
fn literal_library_metadata_scales_with_explicit_statement_count() {
    for size in [4usize, 16, 64, 256] {
        let cpp = format!(
            "#include \"gate.h\"\nint guarded(int n) noexcept {{ {} return n; }}",
            "Gate(n > 0);\n".repeat(size)
        );
        let project = literal_library_fixture(LITERAL_TEXT_HEADER, LITERAL_LIBRARY_HEADER, &cpp);
        refresh_import(&project.config()).unwrap();
        let bytes = fs::metadata(project.artifact()).unwrap().len() as usize;
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
void Guard_constructor(struct Guard* this, int32 n) { owns this->value; ensures this->value == n; } by { execute(); simp(); }
void Guard_destructor(struct Guard* this) { owns this->value; ensures this->value == 0; } by { execute(); simp(); }
int32 checked(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }
int32 guarded(int32& value, int32* untouched) {
    owns value; owns untouched[0..1]; requires value > 0; requires untouched[0] == 7;
    ensures result == old(value); ensures value == old(value); ensures untouched[0] == 7;
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, proof);
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
    let proof = "verifying \"library.cpp\"; int32 guarded(int32 n) { requires n > 0; ensures result == n; } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, proof);
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
        let certificate = |goal: &str| {
            format!(
                r#"arithmetic_certificate rules {{
            premise 0: -9223372036854775808 <= to_integer(a) => -9223372036854775808 <= to_integer(a);
            premise 1: to_integer(a) <= 9223372036854775807 => to_integer(a) <= 9223372036854775807;
            premise 2: 1 <= to_integer(b) => 1 <= to_integer(b);
            premise 3: to_integer(b) <= 2147483647 => to_integer(b) <= 2147483647;
            integer_division_bounds bounds [0, 1, 2, 3] => {goal};
            conclusion 0;
        }}"#
            )
        };
        let expression = format!("{pure}(to_integer(a), to_integer(b))");
        let observed = format!("to_integer(a {op} b)");
        let lower = format!("{lo} <= {expression}");
        let upper = format!("{expression} <= {hi}");
        let lower_cert = certificate(&lower);
        let upper_cert = certificate(&upper);
        let cast_cert = cast_identity_certificate(&observed, lo, hi);
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
    execute();
    have {lo} <= {observed} by {{ arithmetic_certificate rules {{
        premise 0: {observed} == {expression} => {observed} == {expression};
        premise 1: {lower} => {lower};
        integer_relation_transport bounds [0, 1] => {lo} <= {observed}; conclusion 0;
    }} }}
    have {observed} <= {hi} by {{ arithmetic_certificate rules {{
        premise 0: {observed} == {expression} => {observed} == {expression};
        premise 1: {upper} => {upper};
        integer_relation_transport bounds [0, 1] => {observed} <= {hi}; conclusion 0;
    }} }}
    have to_integer(result) == {observed} by {{ {cast_cert} }}
    have to_integer(result) == {expression} by {{ arithmetic_certificate rules {{
        premise 0: {observed} == {expression} => {observed} == {expression};
        premise 1: to_integer(result) == {observed} => to_integer(result) == {observed};
        integer_relation_transport bounds [0, 1] => to_integer(result) == {expression}; conclusion 0;
    }} }}
    simp();
}}
"#
        );
        check_arithmetic_sidecar(&project, &import, &proof);
        for hostile in [
            proof.replace(
                "ensures to_integer(result) ==",
                "ensures to_integer(result) !=",
            ),
            proof.replace("    requires to_integer(a) <= 9223372036854775807;", ""),
            proof.replace("    requires 1 <= to_integer(b);", ""),
            proof.replace("    requires to_integer(b) != 0;", ""),
            proof.replace(
                "integer_division_bounds bounds [0, 1, 2, 3]",
                "integer_division_bounds bounds [0, 1, 3, 2]",
            ),
            proof.replace(
                "integer_relation_transport bounds [0, 1]",
                "integer_relation_transport bounds [1, 0]",
            ),
            proof.replace(
                "integer_cast_identity bounds [0, 1]",
                "integer_cast_identity bounds [0, 0]",
            ),
        ] {
            let path = project.directory.join("false.click");
            fs::write(&path, &hostile).unwrap();
            let parsed = read_click_project(&path, &hostile).unwrap();
            let error = verify_program_prepared_project(&parsed, &import).expect_err(
                "false results, missing guards/bounds and forged certificate references must fail",
            );
            assert!(error.message().len() < 8000, "bounded refusal");
        }
    }
}

#[test]
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
    have to_integer(b) != 0 by {{ arithmetic_certificate rules {{
        premise 0: 1 <= to_integer(b) => 1 <= to_integer(b);
        integer_bound_exclusion bounds [0] => to_integer(b) != 0; conclusion 0;
    }} }}
    have to_integer(b) != -1 by {{ arithmetic_certificate rules {{
        premise 0: 1 <= to_integer(b) => 1 <= to_integer(b);
        integer_bound_exclusion bounds [0] => to_integer(b) != -1; conclusion 0;
    }} }}
    execute(); simp();
}}"#
        );
        check_arithmetic_sidecar(&project, &import, &source);
        for hostile in [
            source.replace("requires 1 <= to_integer(b);", ""),
            source.replace(
                "requires 1 <= to_integer(b);",
                "requires 0 <= to_integer(b);",
            ),
            source.replace(
                "integer_bound_exclusion bounds [0]",
                "integer_bound_exclusion bounds [1]",
            ),
            source.replace(
                "integer_bound_exclusion bounds [0]",
                "integer_bound_exclusion bounds [0, 0]",
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
        let cert = cast_identity_certificate("to_integer(a)", "-100", "100");
        let helper = if name == "relay" { "ss64" } else { name };
        let mut proof = format!(
            r#"verifying "narrow.cpp";
{ty} {helper}(int128 a) {{
    requires -100 <= to_integer(a);
    requires to_integer(a) <= 100;
    ensures -100{suffix} <= result;
    ensures result <= 100{suffix};
}} by {{
    execute();
    have to_integer(result) == to_integer(a) by {{ {cert} }}
    have -100 <= to_integer(result) by {{ arithmetic_certificate rules {{
        premise 0: to_integer(result) == to_integer(a) => to_integer(result) == to_integer(a);
        premise 1: -100 <= to_integer(a) => -100 <= to_integer(a);
        integer_relation_transport bounds [0, 1] => -100 <= to_integer(result); conclusion 0;
    }} }}
    have to_integer(result) <= 100 by {{ arithmetic_certificate rules {{
        premise 0: to_integer(result) == to_integer(a) => to_integer(result) == to_integer(a);
        premise 1: to_integer(a) <= 100 => to_integer(a) <= 100;
        integer_relation_transport bounds [0, 1] => to_integer(result) <= 100; conclusion 0;
    }} }}
    apply({ty}_to_integer_less_equal_implies_less_equal(-100{suffix}, result));
    apply({ty}_to_integer_less_equal_implies_less_equal(result, 100{suffix}));
    simp();
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
} by { execute(); simp(); }
"#,
            );
            check_return_call_sidecar(&project, &import, &proof);
        } else {
            check_arithmetic_sidecar(&project, &import, &proof);
        }
        for hostile in [
            proof.replace("requires -100 <= to_integer(a);", ""),
            proof.replace("requires to_integer(a) <= 100;", ""),
            proof.replace(
                &format!("ensures result <= 100{suffix};"),
                &format!("ensures result <= 99{suffix};"),
            ),
            proof.replace(
                "integer_relation_transport bounds [0, 1]",
                "integer_relation_transport bounds [1, 0]",
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
ensures round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1;
ensures round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
ensures round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1;
ensures round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d));
ensures round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n);
ensures round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d);
ensures round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d);
ensures round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n);
} by { execute(); simp(); }
"#,
        );
        if !rejections {
            check_return_call_sidecar(&project, &import, &proof);
        }
    } else if !rejections {
        check_arithmetic_sidecar(&project, &import, &proof);
    }
    let path = project.directory.join("complete.click");
    fs::write(&path, &proof).unwrap();
    let parsed = read_click_project(&path, &proof).unwrap();
    if !rejections {
        let expanded = expand_project_claim_source_by_label(
            &parsed,
            &ProgramInputs::program(&import),
            "rounded.ensures_0",
        )
        .unwrap();
        verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
        return;
    }
    for hostile in [
            proof.replace(
                "round_down != 0 implies to_integer(result) * to_integer(d) <= to_integer(n)",
                "round_down != 0 implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),
            proof.replace(
                "round_down != 0 implies to_integer(n) < (to_integer(result) + 1) * to_integer(d)",
                "round_down != 0 implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            proof.replace(
                "round_down == 0 implies to_integer(n) <= to_integer(result) * to_integer(d)",
                "round_down == 0 implies to_integer(n) < to_integer(result) * to_integer(d)",
            ),
            proof.replace(
                "round_down == 0 implies (to_integer(result) + -1) * to_integer(d) < to_integer(n)",
                "round_down == 0 implies to_integer(result) * to_integer(d) < to_integer(n)",
            ),

        proof.replace("requires -9223372036854775808 * to_integer(d) <= to_integer(n);", ""),
        proof.replace("requires to_integer(n) <= 9223372036854775807 * to_integer(d);", ""),
        proof.replace("requires -9223372036854775808 * to_integer(d) <= to_integer(n);", "requires -9223372036854775809 * to_integer(d) <= to_integer(n);"),
        proof.replace("requires to_integer(n) <= 9223372036854775807 * to_integer(d);", "requires to_integer(n) <= 9223372036854775808 * to_integer(d);"),
        proof.replace("apply(integer_upper_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), 9223372036854775807));", ""),
        proof.replace("apply(integer_lower_correction_bound(to_integer(n), to_integer(d), to_integer(quot), to_integer(mod), -9223372036854775808));", ""),
        proof.replace("requires d > 0;", ""),
        proof.replace("requires d <= 100;", ""),
        proof.replace("requires d > 0;", "requires d == 0;"),
        proof.replace(
            "ensures -9223372036854775808 <= to_integer(result);",
            "ensures to_integer(result) == 1000;",
        ),
        proof.replace(
            "integer_cast_identity bounds [0, 1]",
            "integer_cast_identity bounds [1, 0]",
        ),
        proof.replace(
            "round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1",
            "round_down != 0 and truncating_remainder(to_integer(n), to_integer(d)) < 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
        ),
        proof.replace(
            "round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
            "round_down == 0 and 0 < truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1",
        ),
        proof.replace(
            "round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d))",
            "round_down != 0 and 0 <= truncating_remainder(to_integer(n), to_integer(d)) implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + 1",
        ),
        proof.replace(
            "round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d))",
            "round_down == 0 and truncating_remainder(to_integer(n), to_integer(d)) <= 0 implies to_integer(result) == truncating_quotient(to_integer(n), to_integer(d)) + -1",
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
#[ignore = "nightly: 6s in the parallel gate"]
fn fee_rounding_pattern_has_checked_native_correction_bounds() {
    check_fee_rounding_pattern("rounded", false);
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn fee_rounding_pattern_modular_caller_has_exact_rounding_values() {
    check_fee_rounding_pattern("caller", false);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn fee_rounding_pattern_rejects_false_rounding_and_missing_guards() {
    check_fee_rounding_pattern("rounded", true);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn fee_rounding_pattern_caller_rejects_false_rounding_and_missing_guards() {
    check_fee_rounding_pattern("caller", true);
}

#[test]
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
} by { execute(); simp(); }
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
fn class_record_proofs_reject_missing_authority_false_frames_and_readonly_writes() {
    let source = include_str!("fixtures/cpp-verification/class-record/class_record.cpp");
    for (selected, original, mutants) in [
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
        assert_eq!(import.export().function.span.file, "header_record.cpp");
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
            "function" => artifact["function"]["span"]["file"] = "state.h".into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
fn cpp_native_record_layouts_retain_distinct_declarations_with_equal_geometry() {
    let source = "struct First { int value; };\nstruct Second { int value; };\nint read_pair(First& first, Second& second) noexcept { return first.value + second.value; }\n";
    let project = Project::with_fixture("pair.cpp", "read_pair", source);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let lowered = lower_import(&import).unwrap();
    let first = &lowered.record_layouts()["First"];
    let second = &lowered.record_layouts()["Second"];
    assert_eq!(first.fields(), second.fields());
    assert_eq!(first.size_bytes(), second.size_bytes());
    assert_eq!(first.alignment_bytes(), second.alignment_bytes());
    assert_ne!(
        first, second,
        "equal geometry does not identify a native record"
    );

    let other = Project::with_fixture("pair.cpp", "read_pair", source);
    refresh_import(&other.config()).unwrap();
    let other_import = load_import(&other.config()).unwrap();
    assert_ne!(import.identity(), other_import.identity());
    let other = lower_import(&other_import).unwrap();
    assert_eq!(first.fields(), other.record_layouts()["First"].fields());
    assert_ne!(
        first,
        &other.record_layouts()["First"],
        "separate locked imports do not establish nominal equivalence"
    );
}

#[test]
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
        let lowered = lower_import(&import).unwrap();
        let boundaries: Vec<_> = lowered.record_layouts()["FeeEnvelope"]
            .records()
            .iter()
            .map(|record| {
                (
                    record.name(),
                    record.offset_bytes(),
                    record.size_bytes(),
                    record.alignment_bytes(),
                    record.parent(),
                )
            })
            .collect();
        assert_eq!(
            boundaries,
            vec![
                ("state", 0, 40, 8, None),
                ("state.left", 0, 16, 8, Some(0)),
                ("state.right", 16, 16, 8, Some(0)),
            ]
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
        check_return_call_sidecar(&project, &load_import(&project.config()).unwrap(), sidecar);
    }
}

#[test]
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
fn nested_record_artifacts_reject_wrong_identity_extent_constness_and_cycles() {
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
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
        ("FeeState* state;", "return stamp;"),
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
    let sidecar = "verifying \"nested.cpp\"; int Envelope_Read(const struct Envelope* this) { ensures result == 0; } by { execute(); simp(); }";
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
        let body = &import.export().function.body;
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
        check_return_call_sidecar(&project, &load_import(&project.config()).unwrap(), sidecar);
    }
}

#[test]
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
        let object = &mut artifact["function"]["body"][0]["object"];
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
                let leaf = artifact["function"]["body"][0]["field"].clone();
                artifact["function"]["body"][0]["object"]["projections"]
                    .as_array_mut()
                    .unwrap()
                    .push(leaf);
            }
            "depth" => {
                let step = object["projections"][0].clone();
                object["projections"] = vec![step; 257].into();
            }
            "readonly" => {
                artifact["function"]["function_kind"]["is_const"] = true.into();
                artifact["function"]["parameters"][0]["value_type"]["pointee"]["is_const"] =
                    true.into();
            }
            "plain_load" => {
                let parameter = artifact["function"]["parameters"][1].clone();
                let span = artifact["function"]["body"][0]["span"].clone();
                artifact["function"]["body"][0]["value"] = serde_json::json!({"kind":"load", "place":{"declaration_id":parameter["declaration_id"], "name":parameter["name"], "span":span, "projections":original["function"]["body"][0]["object"]["projections"]}, "value_type":parameter["value_type"], "span":span});
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock = original_lock.clone();
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
fn nested_pointer_fields_keep_const_object_and_pointee_authority_separate() {
    let source = "struct Child { int* pointer; }; struct Outer { Child child; int stamp; }; int read(const Outer& state, int* value) noexcept { return *state.child.pointer; } void write(const Outer& state, int* value, int next) noexcept { *state.child.pointer = next; }";
    for (selected, sidecar) in [
        (
            "read",
            "verifying \"pointer_nested.cpp\"; int read(const struct Outer& state, int* value) { views state.child.pointer; views value[0..1]; requires state.child.pointer == value; ensures result == value[0]; } by { execute(); simp(); }",
        ),
        (
            "write",
            "verifying \"pointer_nested.cpp\"; void write(const struct Outer& state, int* value, int next) { views state.child.pointer; owns value[0..1]; requires state.child.pointer == value; ensures value[0] == next; ensures state.child.pointer == old(state.child.pointer); } by { execute(); simp(); }",
        ),
    ] {
        let project = Project::with_fixture("pointer_nested.cpp", selected, source);
        refresh_import(&project.config()).unwrap();
        let import = load_import(&project.config()).unwrap();
        // An address equation permits a one-past pointer to `pair.first` to
        // equal `&pair.second`; permission for the latter does not make the
        // former dereferenceable. Retain the original contract as a negative.
        let old_path = project.directory.join("address-only.click");
        fs::write(&old_path, sidecar).unwrap();
        let old = read_click_project(&old_path, sidecar).unwrap();
        assert!(verify_program_prepared_project(&old, &import).is_err());
        // Put the existing pointee authority on the actual loaded carrier.
        // The address equation still supports the unchanged scalar claims.
        let sidecar = sidecar
            .replace("views value[0..1];", "views state.child.pointer[0..1];")
            .replace("owns value[0..1];", "owns state.child.pointer[0..1];");
        check_return_call_sidecar(&project, &import, &sidecar);
        let hostile = sidecar
            .replace("views state.child.pointer[0..1];", "")
            .replace(
                "owns state.child.pointer[0..1];",
                "views state.child.pointer[0..1];",
            );
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
        let arguments = match &import.export().function.body[0] {
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
        check_return_call_sidecar(&project, &load_import(&project.config()).unwrap(), sidecar);
    }
}

#[test]
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
            let place = &mut artifact["function"]["body"][0]["arguments"][0]["place"];
            match change {
                "readonly" => {
                    artifact["function"]["function_kind"]["is_const"] = true.into();
                    artifact["function"]["parameters"][0]["value_type"]["pointee"]["is_const"] =
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
            lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
            lock["artifact_bytes"] = bytes.len().into();
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
        "struct Child { int value; int Read() const noexcept { return value; } }; struct Outer { Child child; }; int run(Outer* root) noexcept { return root->child.Read(); }",
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
        let (_, caller) = sidecar.split_once("} by { execute(); simp(); }").unwrap();
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
#[ignore = "nightly: 2s in the parallel gate"]
fn condition_calls_evaluate_once_before_branch_and_verify_offline() {
    let project = Project::with_fixture("condition.cpp", "choose", CONDITION_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert!(matches!(
        import.export().function.body[0],
        click::languages::cpp::CppStatement::If {
            condition: click::languages::cpp::CppCondition::Call { .. },
            ..
        }
    ));
    fs::remove_file(&project.exporter).unwrap();
    for (answer, expected) in [(0, 2), (1, 1)] {
        let sidecar = format!(
            r#"verifying "condition.cpp";
        bool update(int32& value, bool answer) {{ owns value; requires value == 4; ensures value == 5; ensures result == answer; }} by {{ execute(); simp(); }}
        int32 choose(struct State& state, bool answer) {{ owns state.sibling; views state.left.base.value; requires answer == {answer}; requires state.sibling == 4; ensures result == {expected}; ensures state.sibling == 5; ensures state.left.base.value == old(state.left.base.value); }} by {{ execute(); simp(); }}
        "#
        );
        check_return_call_sidecar(&project, &import, &sidecar);
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn condition_calls_preserve_inherited_receiver_and_sibling_frames() {
    let project = Project::with_fixture("condition.cpp", "observe", CONDITION_CALL_SOURCE);
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    for (value, expected) in [(0, 1), (3, 2)] {
        let sidecar = format!(
            r#"verifying "condition.cpp";
        bool Base_Empty(const struct Base* this) {{ views this->value; ensures result == (if this->value == 0 {{ 1 }} else {{ 0 }}); }} by {{ execute(); simp(); }}
        int32 observe(const struct State& state) {{ views state.left.base.value; views state.sibling; requires state.left.base.value == {value}; ensures result == {expected}; ensures state.sibling == old(state.sibling); }} by {{ execute(); simp(); }}
        "#
        );
        check_return_call_sidecar(&project, &import, &sidecar);
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
        let call = &mut forged["function"]["body"][0]["condition"]["call"];
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
        let helper = if condition == "number()" {
            "int32 number()"
        } else {
            "bool predicate()"
        };
        let sidecar = format!(
            r#"verifying "condition.cpp";
{helper} {{ ensures result == 1; }} by {{ execute(); simp(); }}
int32 choose() {{ ensures result == 1; }} by {{ execute(); simp(); }}
"#
        );
        check_arithmetic_sidecar(&project, &import, &sidecar);
    }
}

#[test]
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
    bool predicate(bool fail) throws int32 { ensures result == 1 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
    int32 choose(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
    "#;
    check_return_call_sidecar(&project, &import, source);
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
    fn guarded_condition(statement: &CStatement) -> bool {
        match statement {
            CStatement::Seq(first, second) => guarded_condition(first) || guarded_condition(second),
            CStatement::TryCatchInt32 {
                try_body,
                handler,
                cleanup_unwind: true,
                ..
            } => {
                contains_call(try_body, "predicate")
                    && matches!(handler.as_ref(), CStatement::Seq(cleanup, rethrow) if contains_call(cleanup, "Guard_destructor") && matches!(rethrow.as_ref(), CStatement::Throw(_)))
            }
            _ => false,
        }
    }
    assert!(guarded_condition(lowered.kernel_function().body()));
}

#[test]
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
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "condition.cpp";
    bool predicate(int32 value) { requires value == 7; ensures result == 1; } by { execute(); simp(); }
    int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
    int32 choose(int32 value) { requires value == 7; ensures result == 9; } by { execute(); simp(); }
    "#,
    );
}

#[test]
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
        bool predicate(bool fail) throws int32 { ensures result == 1 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
        int32 choose(bool fail) { ensures result == 5 or result == 7; } by {
            step();
            outcomes {
                returned => { step(); execute(); simp(); }
                threw => { step(); execute(); simp(); }
            }
        }
    "#;
    check_return_call_sidecar(&project, &import, sidecar);
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
    let operation = artifact["function"]["body"][0].clone();
    let span = artifact["function"]["body"][1]["condition"]["span"].clone();
    artifact["function"]["body"][1]["condition"] = serde_json::json!({"call": {
        "callee": operation["callee"], "arguments": operation["arguments"],
        "value_type": {"kind":"boolean","bits":8,"is_const":false}, "span":span
    }});
    let bytes = serde_json::to_vec(&artifact).unwrap();
    lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
    lock["artifact_bytes"] = bytes.len().into();
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
#[ignore = "nightly: 3s in the parallel gate"]
fn locked_header_graph_conditions_verify_offline_with_inherited_frames() {
    let project = header_graph_project("choose");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    assert_eq!(import.export().function.span.file, "graph.cpp");
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
    for (value, result) in [(0, 1), (3, 3)] {
        let sidecar = format!(
            r#"verifying "graph.cpp";
        bool Base_Empty(const struct Base* this) {{ views this->value; ensures result == (if this->value == 0 {{ 1 }} else {{ 0 }}); }} by {{ execute(); simp(); }}
        bool predicate(const struct Base& state) {{ views state.value; ensures result == (if state.value == 0 {{ 1 }} else {{ 0 }}); }} by {{ execute(); simp(); }}
        int32 Read(const struct Base& state) {{ views state.value; ensures result == state.value; }} by {{ execute(); simp(); }}
        int32 choose(const struct Box& state) {{ views state.left.base.value; views state.sibling; requires state.left.base.value == {value}; ensures result == {result}; ensures state.sibling == old(state.sibling); }} by {{ execute(); simp(); }}
        "#
        );
        check_return_call_sidecar(&project, &import, &sidecar);
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
fn locked_header_graph_mutators_verify_offline_and_require_leaf_authority() {
    let project = header_graph_project("change");
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let sidecar = r#"verifying "graph.cpp";
    void Base_Set(struct Base* this, int32 next) { owns this->value; ensures this->value == next; } by { execute(); simp(); }
    void Store(struct Base& state, int32 next) { owns state.value; ensures state.value == next; } by { execute(); simp(); }
    void change(struct Box& state, int32 next) { owns state.left.base.value; views state.sibling; ensures state.left.base.value == next; ensures state.sibling == old(state.sibling); } by { execute(); simp(); }
    "#;
    check_return_call_sidecar(&project, &import, sidecar);
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
            0 => forged["function"]["span"]["file"] = "helpers.h".into(),
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
            "while (state.value != 0) {} return 0;",
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
    bool predicate(bool fail) throws int32 { ensures result == 1 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
    int32 choose(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
    "#;
    check_return_call_sidecar(&project, &import, sidecar);
    let hostile = sidecar.replace(
        "exceptional ensures exception == 7 by",
        "exceptional ensures exception == 8 by",
    );
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
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "callback.cpp";
    int32 callback(int32 value) { ensures result == value; } by { execute(); simp(); }
    int32 bridge(int32 value) { ensures result == value; } by { execute(); simp(); }
    int32 choose(int32 value) { ensures result == value; } by { execute(); simp(); }
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
    int32 {}(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
    int32 choose(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
    "#,
            callee.name
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
    let cast = &artifact["function"]["body"][0]["initializer"]["conversions"][0];
    assert_eq!(cast["cast_kind"], "no_op");
    assert_eq!(cast["explicit"], true);
    assert_eq!(cast["span"]["file"], "converted.cpp");
    assert_eq!(
        cast["value_type"]["source_aliases"][0]["span"]["file"],
        "converted.h"
    );
    fs::remove_file(&project.exporter).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "converted.cpp";
int64 echo(int64 value) { ensures result == value; } by { execute(); simp(); }
int64 relay(int64 value) { ensures result == value; } by { execute(); simp(); }
"#,
    );
}

#[test]
fn converted_call_initializers_preserve_modulo_narrowing_and_reject_false_fit() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "unsigned long echo(unsigned long value) noexcept { return value; } int relay(unsigned long value) noexcept { int captured = static_cast<int>(echo(value)); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "converted.cpp";
uint64 echo(uint64 value) { ensures result == value; } by { execute(); simp(); }
int32 relay(uint64 value) { requires value == 18446744073709551615u64; ensures result == -1; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
        let conversions = artifact["function"]["body"][0]["initializer"]["conversions"]
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
        check_return_call_sidecar(
            &project,
            &import,
            &format!(
                r#"verifying "converted.cpp";
int32 echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
int64 relay(int32 value) {{ requires value == 7; ensures result == {expected}; }} by {{ execute(); simp(); }}
"#
            ),
        );
    }
}

#[test]
fn converted_call_initializers_evaluate_mutators_once_and_frame_siblings() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "struct Box { int value; int sibling; }; int bump(Box& box) noexcept { box.value = box.value + 1; return box.value; } long relay(Box& box) noexcept { long captured = static_cast<long>(bump(box)); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "converted.cpp";
int32 bump(struct Box& box) { owns box.value; requires box.value == 0; ensures box.value == 1; ensures result == 1; } by { execute(); simp(); }
int64 relay(struct Box& box) { owns box.value; views box.sibling; requires box.value == 0; ensures box.value == 1; ensures result == 1i64; ensures box.sibling == old(box.sibling); } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
        let cast = &mut forged["function"]["body"][0]["initializer"]["conversions"][0];
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
    fn has_cleanup(statement: &CStatement) -> bool {
        match statement {
            CStatement::Seq(first, second) => has_cleanup(first) || has_cleanup(second),
            CStatement::TryCatchInt32 {
                try_body,
                handler,
                cleanup_unwind: true,
                ..
            } => {
                contains_call(try_body, "helper")
                    && matches!(handler.as_ref(), CStatement::Seq(cleanup, rethrow)
                    if contains_call(cleanup, "Guard_destructor") && matches!(rethrow.as_ref(), CStatement::Throw(_)))
            }
            _ => false,
        }
    }
    assert!(has_cleanup(lowered.kernel_function().body()));
}

#[test]
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
int32 helper(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int64 relay(bool fail) throws int32 { ensures result == 5i64 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace("exception == 7 by", "exception == 8 by");
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
int32 next(int32 value) { requires value == 7; ensures result == 8; } by { execute(); simp(); }
int64 relay(int32 value) { requires value == 7; ensures result == 8i64; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
fn converted_call_initializers_preserve_boolean_results() {
    let project = Project::with_fixture(
        "converted.cpp",
        "relay",
        "bool echo(bool value) noexcept { return value; } int relay(bool value) noexcept { int captured = static_cast<int>(echo(value)); return captured; }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "converted.cpp";
bool echo(bool value) { ensures result == value; } by { execute(); simp(); }
int32 relay(bool value) { requires value == 1; ensures result == 1; } by { execute(); simp(); }
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
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "relay.cpp";
int32 echo(int32 value) { ensures result == value; } by { execute(); simp(); }
int64 relay(int32 value) { ensures result == value; } by { execute(); simp(); }
"#,
    );
}

#[test]
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
            "1",
        ),
        (
            "bool",
            "bool",
            "uint64",
            "static_cast<unsigned long>(echo(value))",
            "value == 1",
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
{proof_type} echo({proof_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}
{result_type} relay({proof_type} value) {{ requires {requirement}; ensures result == {expected}; }} by {{ execute(); simp(); }}
"#
        );
        check_return_call_sidecar(&project, &import, &source);
        let hostile = source.replace(
            &format!("ensures result == {expected}"),
            "ensures result == 0",
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
    let cast = &artifact["function"]["body"][0]["conversions"][0];
    assert_eq!(cast["cast_kind"], "no_op");
    assert_eq!(cast["explicit"], true);
    assert_eq!(cast["span"]["file"], "relay.cpp");
    assert_eq!(
        cast["value_type"]["source_aliases"][0]["span"]["file"],
        "relay.h"
    );
    fs::remove_file(&project.exporter).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        r#"verifying "relay.cpp";
int64 echo(int64 value) { ensures result == value; } by { execute(); simp(); }
int64 relay(int64 value) { ensures result == value; } by { execute(); simp(); }
"#,
    );
}

#[test]
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
void Restore_constructor(struct Restore* this, int32* slot) {
 owns this->p; owns this->saved; owns slot[0..1];
 ensures this->p == slot; ensures this->saved == old(slot[0]); ensures slot[0] == 7;
 ensures separate(memory(*this), memory(this->p[0..1]));
} by { execute(); simp(); }
void Restore_destructor(struct Restore* this) {
 requires separate(memory(*this), memory(this->p[0..1]));
 owns this->p; owns this->saved; owns this->p[0..1];
 ensures this->p == old(this->p); ensures this->saved == old(this->saved);
 ensures this->p[0] == old(this->saved);
} by { execute(); simp(); }
int64 read(int32* slot) {
 views slot[0..1]; requires slot[0] == 7; ensures result == 4294967303i64;
 ensures slot[0] == old(slot[0]);
} by { execute(); simp(); }
int32 relay(int32& value) {
 owns value; ensures result == 7; ensures value == old(value);
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
fn converted_return_calls_evaluate_mutators_once_and_preserve_sibling_authority() {
    let project = Project::with_fixture(
        "relay.cpp",
        "relay",
        "struct Box { int value; int sibling; }; long bump(Box& box) noexcept { box.value = box.value + 1; return box.value; } int relay(Box& box) noexcept { return static_cast<int>(bump(box)); }",
    );
    refresh_import(&project.config()).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "relay.cpp";
int64 bump(struct Box& box) { owns box.value; requires box.value == 0; ensures box.value == 1; ensures result == 1i64; } by { execute(); simp(); }
int32 relay(struct Box& box) { owns box.value; views box.sibling; requires box.value == 0; ensures box.value == 1; ensures result == 1; ensures box.sibling == old(box.sibling); } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace("owns box.value; views", "views box.value; views");
    let path = project.directory.join("hostile.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
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
int32 helper(bool fail) throws int32 { ensures result == 5 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
int64 relay(bool fail) throws int32 { ensures result == 5i64 by { execute(); simp(); } exceptional ensures exception == 7 by { execute(); simp(); } }
"#;
    check_return_call_sidecar(&project, &import, source);
    let hostile = source.replace("exception == 7 by", "exception == 8 by");
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
        let returned = &mut forged["function"]["body"][0];
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&forged_lock).unwrap()).unwrap();
        let error = load_import(&project.config()).unwrap_err();
        assert!(error.len() < 8000, "{mutation}: {error}");
    }
}

#[test]
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
int32 echo(int32 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
int32 relay(int32 value) {{ requires value == 0; ensures result == {result}; }} by {{ execute(); simp(); }}
"#
        );
        check_arithmetic_sidecar(&project, &import, &sidecar);
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
    fn has_cleanup(statement: &CStatement) -> bool {
        match statement {
            CStatement::Seq(first, second) => has_cleanup(first) || has_cleanup(second),
            CStatement::TryCatchInt32 {
                try_body,
                handler,
                cleanup_unwind: true,
                ..
            } => {
                contains_call(try_body, "helper")
                    && matches!(handler.as_ref(), CStatement::Seq(cleanup, rethrow)
                    if contains_call(cleanup, "Guard_destructor") && matches!(rethrow.as_ref(), CStatement::Throw(_)))
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
int32 next(int32 value) { requires value == 7; ensures result == 8; } by { execute(); simp(); }
int64 relay(int32 value) { requires value == 7; ensures result == 8i64; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
} by { execute(); simp(); }
contract int32 PositiveRead(const struct State& state) {
    views state.child.value;
    requires state.child.value == 2;
    ensures result == 2;
}
theorem read_application() executes read(const struct State& state) {
    ensures PositiveRead(&read) by {
        have state.child.value > 0 by { arithmetic() using { state.child.value == 2; } }
        execute(); simp();
    }
}
"#;
    let path = project.directory.join("read.click");
    fs::write(&path, source).unwrap();
    let parsed = read_click_project(&path, source).unwrap();
    verify_program_prepared_project(&parsed, &import).unwrap();
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
    let (session, _) =
        C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
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
    // A raw pointer target has no native reference requirement. The wrapper
    // cannot strengthen that target from read's own imported signature.
    let (native, target_and_theorem) = source.split_once("contract int32 PositiveRead").unwrap();
    let weaker = format!(
        "{native}contract int32 PositiveRead{}",
        target_and_theorem
            .replace("const struct State& state", "const struct State* state")
            .replace("state.child.value", "state->child.value")
    );
    fs::write(&path, &weaker).unwrap();
    let error =
        verify_program_prepared_project(&read_click_project(&path, &weaker).unwrap(), &import)
            .unwrap_err();
    assert!(
        error
            .message()
            .contains("could not bind arguments for read"),
        "{}",
        error.message()
    );
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
        let cert = cast_identity_certificate("to_integer(captured)", lo, hi);
        let proof = format!(
            r#"verifying "wide.cpp";
{source} echo({source} value) {{ ensures result == value; }} by {{ execute(); simp(); }}
{result} relay({source} value) {{
 requires {lo} <= to_integer(value); requires to_integer(value) <= {hi};
 ensures to_integer(result) == to_integer(value);
}} by {{
 step();
 let captured = step(echo(value), {{}});
 have {lo} <= to_integer(captured) by {{ arithmetic() using {{ {lo} <= to_integer(value); to_integer(captured) == to_integer(value); }} }}
 have to_integer(captured) <= {hi} by {{ arithmetic() using {{ to_integer(value) <= {hi}; to_integer(captured) == to_integer(value); }} }}
 execute();
 have to_integer(result) == to_integer(captured) by {{ {cert} }}
 arithmetic() using {{ to_integer(result) == to_integer(captured); to_integer(captured) == to_integer(value); }}
}}
"#
        );
        check_return_call_sidecar(&project, &import, &proof);
        if source == "int128" && result == "int64" {
            for hostile in [
                proof.replacen("ensures result == value;", "", 1),
                proof.replace(
                    "integer_cast_identity bounds [0, 1]",
                    "integer_cast_identity bounds [0, 0]",
                ),
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
        for missing in [
            format!("requires {lo} <= to_integer(value);"),
            format!("requires to_integer(value) <= {hi};"),
        ] {
            let hostile = proof.replace(&missing, "");
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
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn converted_wide_return_calls_preserve_values_with_checked_destination_bounds() {
    check_converted_wide_call_results(false);
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn converted_wide_call_initializers_preserve_values_with_checked_destination_bounds() {
    check_converted_wide_call_results(true);
}

#[test]
fn converted_wide_boolean_calls_observe_high_bits() {
    for (point, answer) in [("0", "0"), ("18446744073709551616", "1")] {
        let project = Project::with_fixture(
            "wide.cpp",
            "relay",
            "unsigned __int128 echo(unsigned __int128 value) noexcept { return value; } bool relay(unsigned __int128 value) noexcept { return static_cast<bool>(echo(value)); }",
        );
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let zero_fact = if answer == "0" {
            String::new()
        } else {
            format!(
                "have not (to_integer(captured) == 0) by {{ rewrite(to_integer(captured) == {point}); normalize(); }}"
            )
        };
        let proof = format!(
            r#"verifying "wide.cpp";
uint128 echo(uint128 value) {{ ensures result == value; }} by {{ execute(); simp(); }}
bool relay(uint128 value) {{ requires to_integer(value) == {point}; ensures result == {answer}; }} by {{
 step(); let captured = step(echo(value), {{}});
 have to_integer(captured) == {point} by {{ arithmetic() using {{ to_integer(value) == {point}; to_integer(captured) == to_integer(value); }} }}
 {zero_fact}
 execute(); simp();
}}
"#
        );
        check_return_call_sidecar(&project, &import, &proof);
        let hostile = proof.replace(
            &format!("ensures result == {answer};"),
            &format!(
                "ensures result == {};",
                if answer == "0" { "1" } else { "0" }
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
int32* identity(int32* data) { ensures result == data; } by { execute(); simp(); }
int32* run(int32* data) { ensures result == data; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let hostile = sidecar.replace(
        "ensures result == data; } by",
        "ensures result == data + 1; } by",
    );
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
            0 => forged["function"]["return_type"]["pointee"]["bits"] = 64.into(),
            1 => forged["function"]["return_type"]["pointee"]["is_const"] = true.into(),
            2 => forged["function"]["body"][0]["value_type"]["pointee"]["bits"] = 64.into(),
            3 => forged["reachable_functions"][0]["return_type"]["pointee"]["bits"] = 64.into(),
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
int32& identity(int32& value) { ensures &result == &value; } by { execute(); simp(); }
int32& run(int32& value) { ensures &result == &value; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, aliases);
    let values = aliases.replace(
        "{ ensures &result == &value; }",
        "{ owns value; ensures &result == &value; ensures result == old(value); }",
    );
    check_arithmetic_sidecar(&project, &import, &values);
    check_arithmetic_sidecar(
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
            0 => forged["function"]["return_type"]["kind"] = "pointer".into(),
            1 => forged["function"]["body"][0]["value_type"]["pointee"]["bits"] = 64.into(),
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
int32& run(int32* data) { views data[0..1]; ensures &result == data; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, aliases);
    let values = aliases.replace(
        "ensures &result == data;",
        "ensures &result == data; ensures result == old(data[0]);",
    );
    check_arithmetic_sidecar(&project, &import, &values);
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
int32& helper(int32& value) { ensures &result == &value; } by { execute(); simp(); }
int32& run(int32& value) { owns value; ensures &result == &value; ensures result == 9; ensures value == 9; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
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
    check_arithmetic_sidecar(
        &project,
        &import,
        &proof("step(); step(); step(); have r == 1; have &r == &value; execute(); simp();"),
    );
    for (body, expected) in [
        (
            "step(); step(); step(); have r == 2; execute(); simp();",
            "r == 2",
        ),
        (
            "step(); step(); step(); have r[0] == 1; execute(); simp();",
            "`r` is a reference and names the value it refers to, so it takes no index",
        ),
        (
            "execute_until(assignment(r, 0)); execute(); simp();",
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
/// `load_int32(&value)`.
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
    let text = "verifying \"local.cpp\";\nint32 read(int32& value) { ensures result == result; } by { execute(); simp(); }\n";
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
        !error.message().contains("load_int32(&"),
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
    let text = "verifying \"local.cpp\";\nint32 get(struct cell& c) { views c.second; ensures result == result; } by { execute(); simp(); }\n";
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
        !error.message().contains("load_int32(&"),
        "{}",
        error.message()
    );
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
    let text = "verifying \"local.cpp\";\nint32 pick(int32& value) { views value; ensures result >= 0; } by { execute(); simp(); }\n";
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
    assert!(!expanded.contains("load_int32(&"), "{expanded}");
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
    let text = "verifying \"local.cpp\";\nint32 pick(struct cell& c) { views c.second; ensures result >= 0; } by { execute(); simp(); }\n";
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
        expanded.contains("if at(statement(0).entry, c.second) > "),
        "{expanded}"
    );
    assert!(!expanded.contains("load_int32("), "{expanded}");
    verify_program_prepared_project(&parsed.with_entry_source(expanded.clone()), &import)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
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
const int32& run(int32* data) { views data[0..2]; ensures &result == data + 1; ensures result == old(data[1]); } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, sidecar);
    let hostile = sidecar.replace("views data[0..2];", "views data[0..1];");
    let path = project.directory.join("bad.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
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
int32& run(int32* data) { views data[0..1]; ensures true; } by { execute(); simp(); }
"#;
    let path = project.directory.join("bad.click");
    fs::write(&path, sidecar).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, sidecar).unwrap(), &import)
            .is_err()
    );
    check_arithmetic_sidecar(
        &project,
        &import,
        &sidecar
            .replace("views data[0..1];", "views data[0..2];")
            .replace("ensures true;", "ensures &result == data + 1;"),
    );
}

#[test]
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
const int32& identity(const int32& value) { ensures &result == &value; } by { execute(); simp(); }
const int32& run(const int32& value) { ensures &result == &value; } by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, aliases);
    let values = aliases.replace(
        "{ ensures &result == &value; }",
        "{ views value; ensures &result == &value; ensures result == old(value); }",
    );
    check_arithmetic_sidecar(&project, &import, &values);
    let hostile = aliases.replace("const int32& identity(", "int32& identity(");
    let path = project.directory.join("bad.click");
    fs::write(&path, &hostile).unwrap();
    assert!(
        verify_program_prepared_project(&read_click_project(&path, &hostile).unwrap(), &import)
            .is_err()
    );
}

#[test]
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
    // above: the held range states its own extent limit.
    let source = r#"verifying "bounds.cpp";
int32& run(const struct View& view) {
 views view.data;
 views view.size;
 views view.data[0..view.size];
 requires 1u64 <= view.size;
 ensures &result == view.data + (view.size - 1u64);
 ensures result == old(view.data[view.size - 1u64]);
} by {
 execute(); simp();
}
 "#;
    check_arithmetic_sidecar(&project, &import, source);
}

#[test]
fn direct_subscript_methods_select_and_preserve_reference_authority_offline() {
    let cpp = "struct Cell { int* data; int& operator[](unsigned long index) noexcept { return *data; } }; int& probe(Cell& cell, unsigned long index) noexcept { return cell[index]; }";
    let method = r#"verifying "index.cpp";
int32& Cell_operator_index(struct Cell* this, uint64 index) {
 views this->data;
 views this->data[0..1];
 ensures &result == this->data;
 ensures result == old(this->data[0]);
} by { execute(); simp(); }
"#;
    let caller = r#"int32& probe(struct Cell& cell, uint64 index) {
 views cell.data;
 views cell.data[0..1];
 ensures &result == cell.data;
 ensures result == old(cell.data[0]);
} by { execute(); simp(); }
"#;
    for selector in ["Cell::operator[]", "probe"] {
        let project = Project::with_fixture("index.cpp", selector, cpp);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        assert!(
            import.export().function.name == "Cell_operator_index"
                || import.export().function.name == "probe"
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
fn cpp_external_backing_reference_survives_descriptor_destruction_offline() {
    check_cpp_descriptor_backing_lifetime(false);
}

#[test]
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
void View_constructor(struct View* this, int32* input) {
 owns this->data;
 ensures this->data == input;
} by { execute(); simp(); }
void View_destructor(struct View* this) {
 owns this->data;
} by { execute(); simp(); }
int32& View_get(const struct View* this) {
 views this->data;
 views this->data[0..1];
 ensures &result == this->data;
 ensures result == old(this->data[0]);
} by { execute(); simp(); }
int32& run(int32* data) {
 views data[0..1];
 ensures &result == data;
 ensures result == old(data[0]);
} by { execute(); simp(); }
"#;
    let source = if writes {
        format!(
            "{source}{}",
            r#"
int32 write(int32* data, int32 input) {
 owns data[0..1];
 ensures result == input;
 ensures data[0] == input;
} by { execute(); simp(); }
"#
        )
    } else {
        source.to_owned()
    };
    let source = source.as_str();
    check_return_call_sidecar(&project, &import, source);
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
int32* run() { ensures result == 0; } by { execute(); simp(); }
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
int32 read(int32* data) { views data[0..1]; ensures result == data[0]; } by { execute(); simp(); }
int32 run() { ensures 1 == 1; } by { execute(); simp(); }
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
            "const int* run() noexcept { return nullptr; }",
            "mutable int32 pointer",
        ),
        (
            "long long* run() noexcept { return nullptr; }",
            "mutable int32 pointer",
        ),
    ] {
        let project = Project::with_fixture("null.cpp", "run", cpp);
        let error = refresh_import(&project.config()).unwrap_err();
        assert!(error.contains(message), "{error}");
        assert!(!project.artifact().exists());
    }
}

#[test]
fn cpp_reference_into_destroyed_local_backing_cannot_be_read_offline() {
    let cpp = "struct Cell { int value; int state; explicit Cell(int input) noexcept : value(input), state(1) {} ~Cell() noexcept { state = 0; } int& get() noexcept { return value; } }; int& run(int input) noexcept { Cell cell(input); return cell.get(); }";
    let project = Project::with_fixture("expired.cpp", "run", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "expired.cpp";
void Cell_constructor(struct Cell* this, int32 input) {
 owns this->value;
 owns this->state;
 ensures this->value == input;
 ensures this->state == 1;
} by { execute(); simp(); }
void Cell_destructor(struct Cell* this) {
 owns this->state;
 ensures this->state == 0;
} by { execute(); simp(); }
int32& Cell_get(struct Cell* this) {
 views this->value;
 ensures &result == &this->value;
 ensures result == old(this->value);
} by { execute(); simp(); }
int32& run(int32 input) { ensures result == input; } by { execute(); simp(); }
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
fn cpp_field_reference_results_preserve_addresses_and_backing_authority_offline() {
    let cpp = "struct Cell { int value; int& get() noexcept { return value; } }; int write(Cell& cell, int input) noexcept { int& element = cell.get(); element = input; return element; }";
    let project = Project::with_fixture("field.cpp", "write", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "field.cpp";
int32& Cell_get(struct Cell* this) {
 views this->value;
 ensures &result == &this->value;
 ensures result == old(this->value);
} by { execute(); simp(); }
int32 write(struct Cell& cell, int32 input) {
 owns cell.value;
 ensures result == input;
 ensures cell.value == input;
} by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
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
fn cpp_const_field_reference_results_retain_qualification_offline() {
    let cpp = "struct Cell { int value; const int& get() const noexcept { return value; } }; const int& run(const Cell& cell) noexcept { return cell.get(); }";
    let project = Project::with_fixture("field.cpp", "run", cpp);
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let source = r#"verifying "field.cpp";
const int32& Cell_get(const struct Cell* this) {
 views this->value;
 ensures &result == &this->value;
 ensures result == old(this->value);
} by { execute(); simp(); }
const int32& run(const struct Cell& cell) {
 views cell.value;
 ensures &result == &cell.value;
 ensures result == old(cell.value);
} by { execute(); simp(); }
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
int32* run(int32* input) { ensures result == input; } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, source);
}

// The child constructor is a modular call into the parent's field storage.
// Its generic proof cannot assume that the child's allocation ends there.
#[test]
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
void Extent_constructor(struct Extent* this, uint64 input) {
 owns this->size;
 ensures this->size == input;
} by { execute(); simp(); }
void View_constructor(struct View* this, int32* backing, uint64 count) {
 owns this->data;
 owns this->extent.size;
 ensures this->data == backing;
 ensures this->extent.size == count;
} by { execute(); simp(); }
uint64 probe(int32* backing, uint64 count) {
 views backing[0];
 ensures result == count;
 ensures backing[0] == old(backing[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    for label in [
        "Extent_constructor.contract",
        "View_constructor.contract",
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
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
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
void Node_constructor(struct Node* this, int32 input) {
 owns this->self;
 owns this->value;
 ensures this->self == &this->value;
 ensures this->value == input;
} by { execute(); simp(); }
void Parent_constructor(struct Parent* this, int32 input) {
 owns this->prefix;
 owns this->child.self;
 owns this->child.value;
 ensures this->prefix == 7;
 ensures this->child.self == &this->child.value;
 ensures this->child.value == input;
} by { execute(); simp(); }
int32 probe(int32 input) {
 ensures result == input;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
}

// Locked, instantiated header constructors retain ordinary checked calls,
// including an observer initializer before nested member construction.
#[test]
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
int32* address(int32* value) { ensures result == value; } by { execute(); simp(); }
void Extent_constructor(struct Extent* this, uint64 input) {
 owns this->size;
 ensures this->size == input;
} by { execute(); simp(); }
void Descriptor_constructor(struct Descriptor* this, int32* backing, uint64 count) {
 owns this->data;
 owns this->extent.size;
 ensures this->data == backing;
 ensures this->extent.size == count;
} by { execute(); simp(); }
uint64 probe(int32* backing, uint64 count) {
 views backing[0];
 ensures result == count;
 ensures backing[0] == old(backing[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "Descriptor_constructor.contract",
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
fn construction_return_descriptor_factories_verify_offline() {
    check_construction_return_descriptor_factories(false);
}

#[test]
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
        import.export().function.body[0],
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
        click::kernel::CAggregateReturnMode::Construction
    );
    let proof = r#"verifying "construct-return.cpp";
int32* identity(int32* p) { ensures result == p; } by { execute(); simp(); }
int32* address(int32* p) { ensures result == p; } by { execute(); simp(); }
void Extent_constructor(struct Extent* this, uint64 n) {
 owns this->size;
 ensures this->size == n;
} by { execute(); simp(); }
void View_constructor(struct View* this, int32* p, uint64 n) {
 owns this->data;
 owns this->extent.size;
 ensures this->data == p;
 ensures this->extent.size == n;
} by { execute(); simp(); }
struct View make(int32* p, uint64 n) {
 ensures result.data == p;
 ensures result.extent.size == n;
} by { execute(); simp(); }
struct View forward(int32* p, uint64 n) {
 ensures result.data == p;
 ensures result.extent.size == n;
} by { execute(); simp(); }
struct View relay(int32* p, uint64 n) {
 ensures result.data == p;
 ensures result.extent.size == n;
} by { execute(); simp(); }
uint64 probe(int32* p, uint64 n) {
 views p[0..1];
 ensures result == n;
 ensures p[0] == old(p[0]);
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
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
        C0VerificationSession::new_program_prepared_project(&whole, &import).unwrap();
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
            0 => forged["function"]["body"][0]["value_type"]["name"] = "Other".into(),
            1 => forged["function"]["body"][0]["callee"]["declaration_id"] = "missing".into(),
            2 => forged["function"]["body"][0]["arguments"] = serde_json::json!([]),
            3 => {
                forged["function"]["body"][0]["cleanups"] = serde_json::json!([{
                    "kind": "destructor",
                "object": {"declaration_id":artifact["function"]["parameters"][0]["declaration_id"],
                           "name":artifact["function"]["parameters"][0]["name"],
                           "span":artifact["function"]["parameters"][0]["span"]},
                "callee":artifact["function"]["body"][0]["callee"],
                "span":artifact["function"]["body"][0]["span"]
                }])
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec_pretty(&forged).unwrap();
        let mut forged_lock = lock.clone();
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
fn construction_assignment_materializes_rhs_and_preserves_backing_offline() {
    check_construction_assignment(false);
}

#[test]
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
        import.export().function.body[1],
        click::languages::cpp::CppStatement::AssignConstructionCall { .. }
    ));
    let proof = r#"verifying "construct-assignment.cpp";
int32* identity(int32* p) { ensures result == p; } by { execute(); simp(); }
void View_constructor(struct View* this, int32* p, uint64 n) {
 owns this->data;
 owns this->size;
 ensures this->data == p;
 ensures this->size == n;
} by { execute(); simp(); }
struct View resize(const struct View& view, uint64 n) {
 views view.data;
 ensures result.data == old(view.data);
 ensures result.size == n;
 ensures view.data == old(view.data);
} by { execute(); simp(); }
uint64 probe(struct View& view, uint64 n) {
 owns view.data;
 owns view.size;
 owns view.data[0..1];
 ensures result == n;
 ensures view.data == old(view.data);
 ensures view.size == n;
 ensures view.data[0] == 19;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
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
        C0VerificationSession::new_program_prepared_project(&whole, &import).unwrap();
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
        import.export().function.body[1],
        click::languages::cpp::CppStatement::AssignConstructionCall { .. }
    ));
    let proof = r#"verifying "construct-assignment.cpp";
int32* identity(int32* p) { ensures result == p; } by { execute(); simp(); }
void View_constructor(struct View* this, int32* p, uint64 n) {
 owns this->data;
 owns this->size;
 ensures this->data == p;
 ensures this->size == n;
} by { execute(); simp(); }
struct View resize(const struct View& view, uint64 n) {
 views view.data;
 ensures result.data == old(view.data);
 ensures result.size == n;
 ensures view.data == old(view.data);
} by { execute(); simp(); }
int32& probe(struct View& view, uint64 n) {
 owns view.data;
 owns view.size;
 views view.data[0..1];
 ensures &result == old(view.data);
 ensures result == old(view.data[0]);
 ensures view.data == old(view.data);
 ensures view.size == n;

} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
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
        import.export().function.body[2],
        click::languages::cpp::CppStatement::AssignConstructionCall { .. }
    ));
    let proof = r#"verifying "construct-assignment.cpp";
int32* identity(int32* p) { ensures result == p; } by { execute(); simp(); }
void View_constructor(struct View* this, int32* p, int32 n) {
 owns this->data;
 owns this->size;
 ensures this->data == p;
 ensures this->size == n;
} by { execute(); simp(); }
struct View resize(const struct View& view, int32 n) {
 views view.data;
 ensures result.data == old(view.data);
 ensures result.size == n;
 ensures view.data == old(view.data);
} by { execute(); simp(); }
int32& last(const struct View& view) {
 views view.data;
 views view.size;
 views view.data[0..view.size];
 requires 1 <= view.size;
 requires view.size <= 1073741823;
 ensures &result == old(view.data) + (old(view.size) - 1);
 ensures result == old(view.data[view.size - 1]);
} by { have 0 <= view.size - 1 by { arithmetic() using { 1 <= view.size; view.size <= 1073741823; } } have view.size - 1 < view.size by { arithmetic() using { 1 <= view.size; view.size <= 1073741823; } } execute(); simp(); }
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

} by { have 0 <= view.size - 1 by { arithmetic() using { 1 <= view.size; view.size <= 1073741823; } } have view.size - 1 < view.size by { arithmetic() using { 1 <= view.size; view.size <= 1073741823; } } execute(); simp(); }
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
fn returned_constructor_composed_observers_verify_and_reject_writes_offline() {
    let project = Project::with_fixture(
        "observe-result.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; struct Box { unsigned long value; explicit Box(unsigned long input) noexcept : value(input) {} }; Box probe(const Count& count) noexcept { return Box(count.size() + 1UL); }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "observe-result.cpp";
uint64 Count_size(const struct Count* this) { views this->value; ensures result == this->value; } by { execute(); simp(); }
void Box_constructor(struct Box* this, uint64 input) { owns this->value; ensures this->value == input; } by { execute(); simp(); }
struct Box probe(const struct Count& count) { views count.value; ensures result.value == count.value + 1u64; ensures count.value == old(count.value); } by { execute(); simp(); }
"#;
    check_return_call_sidecar(&project, &import, proof);
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
    let proof = "verifying \"sentinel.cpp\"; uint64 probe() { ensures result == 18446744073709551615u64; } by { execute(); simp(); }";
    check_arithmetic_sidecar(&project, &import, proof);
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
        forged_lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        forged_lock["artifact_bytes"] = bytes.len().into();
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
fn scalar_assignment_observers_verify_and_reject_writes_offline() {
    let project = Project::with_fixture(
        "assign-observer.cpp",
        "probe",
        "struct Count { unsigned long value; unsigned long size() const noexcept { return value; } }; unsigned long probe(const Count& count, unsigned long n) noexcept { n = count.size() + 1UL; return n; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"assign-observer.cpp\"; uint64 Count_size(const struct Count* this) { views this->value; ensures result == this->value; } by { execute(); simp(); } uint64 probe(const struct Count& count, uint64 n) { views count.value; ensures result == count.value + 1u64; ensures count.value == old(count.value); } by { execute(); simp(); }";
    check_return_call_sidecar(&project, &import, proof);
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
fn cpp_native_word_and_byte_pointer_stores_verify_offline() {
    for (source_type, contract_type, literal) in [
        ("unsigned int", "uint32", "4294967295u32"),
        ("unsigned char", "uint8", "255u8"),
    ] {
        let source = format!(
            "{source_type} probe({source_type}* p, {source_type} value) noexcept {{ *(p + 1) = value; return *(p + 1); }}"
        );
        let project = Project::with_fixture("pointer.cpp", "probe", &source);
        refresh_import(&project.config()).unwrap();
        fs::remove_file(&project.exporter).unwrap();
        let import = load_import(&project.config()).unwrap();
        let sidecar = format!(
            "verifying \"pointer.cpp\"; {contract_type} probe({contract_type}* p, {contract_type} value) {{ owns p[0..2]; requires value == {literal}; ensures p[1] == value; ensures p[0] == old(p[0]); ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &sidecar);
        let bad = sidecar.replace("owns p[0..2];", "views p[0..2];");
        let path = project.directory.join("bad.click");
        fs::write(&path, &bad).unwrap();
        let parsed = read_click_project(&path, &bad).unwrap();
        assert!(verify_program_prepared_project(&parsed, &import).is_err());
    }
}

#[test]
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
            "verifying \"address.cpp\"; {contract_type} probe({contract_type} value) {{ ensures result == value; }} by {{ execute(); simp(); }}"
        );
        check_return_call_sidecar(&project, &import, &sidecar);
    }
}

#[test]
fn cpp_native_byte_field_address_uses_one_byte_storage_offline() {
    let project = Project::with_fixture(
        "field.cpp",
        "probe",
        "struct Pair { unsigned char a; unsigned char b; }; unsigned char probe(Pair& pair, unsigned char value) noexcept { *(&pair.b) = value; return pair.b; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"field.cpp\"; uint8 probe(struct Pair& pair, uint8 value) { owns pair.b; ensures pair.b == value; ensures result == value; } by { execute(); simp(); }",
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
                artifact["function"]["parameters"][0]["value_type"]["pointee"]["bits"] = 32.into();
                artifact["function"]["body"][0]["arguments"][0]["value"]["value_type"]["pointee"]
                    ["bits"] = 32.into();
            }
            _ => unreachable!(),
        }
        let bytes = serde_json::to_vec(&artifact).unwrap();
        let mut lock = original_lock.clone();
        lock["artifact_sha256"] = format!("{:x}", Sha256::digest(&bytes)).into();
        lock["artifact_bytes"] = bytes.len().into();
        fs::write(project.artifact(), bytes).unwrap();
        fs::write(project.lock(), serde_json::to_vec(&lock).unwrap()).unwrap();
        assert!(load_import(&project.config()).is_err(), "{change}");
    }
}

// Scalar allocation ownership can enter and return from a modular write.
// Ownership alone must not let a call read an uninitialized local.
#[test]
fn cpp_native_scalar_modular_write_uses_allocation_ownership_offline() {
    let project = Project::with_fixture(
        "initialize.cpp",
        "probe",
        "void fill(unsigned int* p, unsigned int value) noexcept { *p = value; } unsigned int probe(unsigned int value) noexcept { unsigned int obj = 0; fill(&obj, value); return obj; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = "verifying \"initialize.cpp\"; void fill(uint32* p, uint32 value) { owns p[0..1]; ensures p[0] == value; } by { execute(); simp(); } uint32 probe(uint32 value) { ensures result == value; } by { execute(); simp(); }";
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
    let proof = "verifying \"initialize.cpp\"; void fill(uint32* p, uint32 value) { owns p[0..1]; ensures p[0] == value; } by { execute(); simp(); } uint32 probe(uint32 value) { ensures result == value; } by { execute(); simp(); }";
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
    let assumed = format!(
        "verifying \"driver.cpp\";\nextern int32* {}(int32* p) {{ ensures result == p; }}\nint32* forward(int32* p) {{ ensures result == p; }} by {{ execute(); simp(); }}\n",
        axiom.name
    );
    fs::write(&sidecar, &assumed).unwrap();
    let parsed = read_click_project(&sidecar, &assumed).unwrap();
    verify_program_prepared_project(&parsed, &import)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    let unassumed = "verifying \"driver.cpp\";\nint32* forward(int32* p) { ensures result == p; } by { execute(); simp(); }\n";
    fs::write(&sidecar, unassumed).unwrap();
    let parsed = read_click_project(&sidecar, unassumed).unwrap();
    let error = verify_program_prepared_project(&parsed, &import).unwrap_err();
    assert!(error.message().contains(&axiom.name), "{}", error.message());

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
    check_return_call_sidecar(
        &project,
        &import,
        "verifying \"pointer-local.cpp\"; uint8* probe(uint8* p, uint8* q) { ensures result == q; } by { execute(); simp(); }",
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
        "verifying \"bump_reference.cpp\"; int32 bump_reference(int32& value) { views value; ensures result == value; ensures value == old(value); } by { execute(); simp(); }",
    );
}

#[test]
fn trivial_record_prvalue_arguments_import_with_full_expression_storage() {
    for (file, source) in [
        (
            "direct_record_argument.cpp",
            "struct View { int* pointer; int count; View(int* p, int n) noexcept : pointer(p), count(n) {} }; int consume(View view) noexcept { return view.count; } int probe() noexcept { int value = 7; return consume(View(&value, 1)); }",
        ),
        (
            "nested_record_argument.cpp",
            "struct View { int* pointer; int count; View(int* p, int n) noexcept : pointer(p), count(n) {} }; View make(int* p, int n) noexcept { return View(p, n); } struct Reader { int state; int read(View view) noexcept { return view.count; } }; int probe() noexcept { int value = 7; Reader reader{0}; return reader.read(make(&value, 1)); }",
        ),
    ] {
        let project = Project::with_fixture(file, "probe", source);
        refresh_import(&project.config())
            .expect("complete copy-equivalent record argument must import");
        let import = load_import(&project.config()).unwrap();
        assert!(!import.export().function.body.is_empty());
        fs::remove_file(&project.exporter).unwrap();
        let mut proof = format!(
            "verifying \"{file}\";\nvoid View_constructor(struct View* this, int32* p, int32 n) {{ owns this->pointer; owns this->count; ensures this->pointer == p; ensures this->count == n; }} by {{ execute(); simp(); }}\n"
        );
        if file == "direct_record_argument.cpp" {
            proof.push_str("int32 consume(struct View view) { ensures result == view.count; } by { execute(); simp(); }\n");
        } else {
            proof.push_str("struct View make(int32* p, int32 n) { ensures result.pointer == p; ensures result.count == n; } by { execute(); simp(); }\nint32 Reader_read(struct Reader* this, struct View view) { ensures result == view.count; } by { execute(); simp(); }\n");
        }
        proof.push_str("int32 probe() { ensures result == 1; } by { execute(); simp(); }\n");
        check_arithmetic_sidecar(&project, &import, &proof);
        let parsed =
            read_click_project(&project.directory.join("arithmetic.click"), &proof).unwrap();
        let expanded = expand_project_claim_source_by_label(
            &parsed,
            &ProgramInputs::program(&import),
            "probe.contract",
        )
        .unwrap();
        let rewritten = parsed.with_entry_source(expanded.clone());
        verify_program_prepared_project(&rewritten, &import).unwrap();
        let (session, _) =
            C0VerificationSession::new_program_prepared_project(&parsed, &import).unwrap();
        let position = project_tactic_source_position(
            &rewritten,
            &ProgramInputs::program(&import),
            "probe.contract",
            0,
        )
        .unwrap();
        session
            .verify_at_project(&expanded, position.line, position.column)
            .unwrap();
    }
}

#[test]
fn record_prvalue_argument_rejects_storage_sensitive_construction_and_unordered_calls() {
    for (source, expected) in [
        (
            "struct Node { int* self; int value; Node(int n) noexcept : self(&value), value(n) {} }; int consume(Node node) noexcept { return node.value; } int probe() noexcept { return consume(Node(7)); }",
            "copy-equivalent",
        ),
        (
            "struct View { int value; View(int n) noexcept : value(n) {} }; View make(int n) noexcept { return View(n); } int consume(View left, View right) noexcept { return left.value + right.value; } int probe() noexcept { return consume(make(1), make(2)); }",
            "one call",
        ),
    ] {
        let project = Project::with_fixture("record_argument_refusal.cpp", "probe", source);
        let error = refresh_import(&project.config())
            .expect_err("argument source semantics must not be weakened");
        assert!(error.contains(expected), "unexpected refusal: {error}");
    }
}

#[test]
fn imported_pointer_field_setter_keeps_checked_carrier_during_selected_expansion() {
    let project = Project::with_fixture(
        "setter.cpp",
        "probe",
        r#"
struct Holder {
    int* saved;
    explicit Holder(int* initial) noexcept : saved(initial) {}
    void set(int* input) noexcept { saved = input; }
};
int probe(int input) noexcept {
    int value = input;
    int initial = 0;
    Holder holder(&initial);
    holder.set(&value);
    return *holder.saved;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "setter.cpp";
void Holder_constructor(struct Holder* this, int32* initial) {
    owns this->saved;
    ensures this->saved == initial;
} by { execute(); simp(); }
void Holder_set(struct Holder* this, int32* input) {
    owns this->saved;
    ensures this->saved == input;
} by { execute(); simp(); }
int32 probe(int32 input) {
    ensures result == input;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
}

#[test]
fn imported_cpp_valid_place_checks_scalar_and_record_guarantees_offline() {
    let project = Project::with_fixture(
        "setter.cpp",
        "probe",
        r#"
struct Holder {
    int* saved;
    explicit Holder(int* initial) noexcept : saved(initial) {}
    void set(int* input) noexcept { saved = input; }
};
int probe(int input) noexcept {
    int value = input;
    int initial = 0;
    Holder holder(&initial);
    holder.set(&value);
    return *holder.saved;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "setter.cpp";
void Holder_constructor(struct Holder* this, int32* initial) {
    owns this->saved;
    ensures this->saved == initial;
} by { execute(); simp(); }
void Holder_set(struct Holder* this, int32* input) {
    owns this->saved;
    requires valid_place(this);
    requires valid_place(input);
    ensures valid_place(this);
    ensures this->saved == input;
} by { execute(); simp(); }
int32 probe(int32 input) {
    ensures result == input;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "Holder_set.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
}

#[test]
fn imported_pointer_field_setter_wrapper_keeps_checked_carrier_during_selected_expansion() {
    let project = Project::with_fixture(
        "setter.cpp",
        "probe",
        r#"
struct Holder {
    int* saved;
    explicit Holder(int* initial) noexcept : saved(initial) {}
    void set(int* input) noexcept { saved = input; }
};
void relay(Holder& holder, int* input) noexcept { holder.set(input); }
int probe(int input) noexcept {
    int value = input;
    int initial = 0;
    Holder holder(&initial);
    relay(holder, &value);
    return *holder.saved;
}
"#,
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    let proof = r#"verifying "setter.cpp";
void Holder_constructor(struct Holder* this, int32* initial) {
    owns this->saved;
    ensures this->saved == initial;
} by { execute(); simp(); }
void Holder_set(struct Holder* this, int32* input) {
    owns this->saved;
    ensures this->saved == input;
} by { execute(); simp(); }
void relay(struct Holder& holder, int32* input) {
    owns holder.saved;
    ensures holder.saved == input;
} by { execute(); simp(); }
int32 probe(int32 input) {
    ensures result == input;
} by { execute(); simp(); }
"#;
    check_arithmetic_sidecar(&project, &import, proof);
    let parsed = read_click_project(&project.directory.join("arithmetic.click"), proof).unwrap();
    let expanded = expand_project_claim_source_by_label(
        &parsed,
        &ProgramInputs::program(&import),
        "probe.contract",
    )
    .unwrap();
    verify_program_prepared_project(&parsed.with_entry_source(expanded), &import).unwrap();
}

#[test]
fn unsigned_word_pointer_and_embedded_extent_copy_by_value_offline() {
    let project = Project::with_fixture(
        "word-view.cpp",
        "probe",
        "struct Extent { unsigned long count; }; struct View { unsigned int* pointer; Extent extent; }; unsigned long probe(View value) noexcept { return value.extent.count; }",
    );
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    let import = load_import(&project.config()).unwrap();
    check_arithmetic_sidecar(
        &project,
        &import,
        "verifying \"word-view.cpp\"; uint64 probe(struct View value) { ensures result == value.extent.count; } by { execute(); simp(); }",
    );
}
