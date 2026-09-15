use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use click::cli::{CInput, read_c_inputs, read_click_project};
use click::kernel::{
    Bitvector32Term, CExpression, CFunctionOutcome, CMemory, CMemoryRange, CResourceFact, CState,
    CStatement, CType, CUndefinedBehavior, Pointer, PointerOffsetTerm, Proposition,
    PureFactContext, ResourceContext, c_typed_pointer_value, int32,
    prove_symbolic_c_function_execution,
};
use click::languages::cpp::{
    CppBinaryOperator, CppCallArgument, CppCleanup, CppExpression, CppFunctionKind, CppInitializer,
    CppStatement, CppType, load_import, lower_import, refresh_import,
};
use click::surface::{
    C0VerificationSession, VerifiedClaim, cpp_prepared_project_smart_tactic_source_sites,
    cpp_prepared_project_tactic_source_position, expand_cpp_prepared_project_tactic_source_at,
    verify_cpp_prepared_project,
};

const SOURCE: &str = include_str!("fixtures/cpp-verification/increment/increment.cpp");
const SIDECAR: &str = include_str!("fixtures/cpp-verification/increment/increment.click");
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

struct Project {
    directory: PathBuf,
    exporter: PathBuf,
    source_name: String,
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
        };
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

    fn write_config(&self, function: &str) {
        let config = serde_json::json!({
            "schema": 1,
            "language": "c++",
            "standard": "c++20",
            "target": "x86_64-unknown-linux-gnu",
            "exceptions": false,
            "rtti": false,
            "exporter": self.exporter,
            "working_directory": ".",
            "source": &self.source_name,
            "logical_source": &self.source_name,
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
    let first_artifact = fs::read(project.artifact()).unwrap();
    let first_lock = fs::read(project.lock()).unwrap();
    refresh_import(&project.config()).expect("repeat the same semantic export");
    assert_eq!(fs::read(project.artifact()).unwrap(), first_artifact);
    assert_eq!(fs::read(project.lock()).unwrap(), first_lock);

    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");
    let prepared = load_import(&project.config()).expect("locked loading must not execute Clang");
    assert_eq!(prepared.export().schema, 9);
    assert!(prepared.export().reachable_functions.is_empty());
    assert_eq!(prepared.logical_source(), "increment.cpp");
    assert_eq!(prepared.identity().len(), 64);
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
fn locked_cpp_function_verifies_through_the_shared_sidecar_path_offline() {
    let project = Project::new();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, SIDECAR).unwrap();
    refresh_import(&project.config()).expect("refresh the C++ import explicitly");
    fs::remove_file(&project.exporter).expect("make the exporter unavailable after refresh");

    let click_source = fs::read_to_string(&sidecar).unwrap();
    let inputs = read_c_inputs(&sidecar, &click_source).expect("load the locked sidecar input");
    let CInput::PreparedCpp(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("verify the directly lowered C++ function");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
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
    let CInput::PreparedCpp(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("verify both C++ return paths against one contract");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 0, 1, 2],
        "both return paths certify returned ownership and both postconditions"
    );

    let sites = cpp_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
    );
    let execute =
        cpp_prepared_project_tactic_source_position(&click_project, &import, "choose.contract", 0)
            .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the branch execution into a checkable source proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_cpp_prepared_project(&rewritten, &import)
        .expect("the expanded branch proof must reverify");
    let (session, _) = C0VerificationSession::new_cpp_prepared_project(&click_project, &import)
        .expect("retain the original branch verification environment");
    let next =
        cpp_prepared_project_tactic_source_position(&rewritten, &import, "choose.contract", 0)
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
    let CInput::PreparedCpp(import) = inputs else {
        panic!("language=c++ must select the C++ prepared-input path")
    };
    let click_project = read_click_project(&sidecar, &click_source).unwrap();
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("one owned cell should authorize an aliased mutable write and const read");
    assert_eq!(
        verified
            .iter()
            .map(|theorem| match theorem.claim {
                VerifiedClaim::Ensure { index, .. } => index,
            })
            .collect::<Vec<_>>(),
        vec![0, 1, 2],
        "the proof returns ownership and checks both postconditions without an inferred view"
    );

    let sites = cpp_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
    );
    let execute = cpp_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "write_then_read.contract",
        0,
    )
    .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the aliased reference execution into a checkable proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_cpp_prepared_project(&rewritten, &import)
        .expect("the expanded const-reference proof must reverify");
    let (session, _) = C0VerificationSession::new_cpp_prepared_project(&click_project, &import)
        .expect("retain the const-reference verification environment");
    let next = cpp_prepared_project_tactic_source_position(
        &rewritten,
        &import,
        "write_then_read.contract",
        0,
    )
    .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded const-reference proof");

    let mutable_signature =
        CONST_REFERENCE_SIDECAR.replace("const int32* readable", "int32* readable");
    fs::write(&sidecar, &mutable_signature).unwrap();
    let mismatched_project = read_click_project(&sidecar, &mutable_signature).unwrap();
    let error = verify_cpp_prepared_project(&mismatched_project, &import).unwrap_err();
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
        CStatement::Call { function_name, .. } => function_name == expected,
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

fn contains_aggregate_construction_begin(statement: &CStatement, expected: &str) -> bool {
    match statement {
        CStatement::DeclareAggregate {
            name,
            construction: true,
            ..
        } => name == expected,
        CStatement::Seq(first, second) => {
            contains_aggregate_construction_begin(first, expected)
                || contains_aggregate_construction_begin(second, expected)
        }
        CStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            contains_aggregate_construction_begin(then_branch, expected)
                || contains_aggregate_construction_begin(else_branch, expected)
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
    assert_eq!(import.export().schema, 9);
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
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("verify the helper and caller through shared modular call rules");
    assert_eq!(verified.len(), 6);

    let sites = cpp_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp", "execute", "simp"]
    );
    let execute = cpp_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "call_set_seven.contract",
        0,
    )
    .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the caller's modular execution proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_cpp_prepared_project(&rewritten, &import)
        .expect("the expanded modular C++ proof must reverify");
    let (session, _) = C0VerificationSession::new_cpp_prepared_project(&click_project, &import)
        .expect("retain the modular C++ verification environment");
    let next = cpp_prepared_project_tactic_source_position(
        &rewritten,
        &import,
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
    assert_eq!(import.export().schema, 9);
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
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("verify local initialization through the shared call-result rule");
    assert_eq!(verified.len(), 5);

    let execute = cpp_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "relay_value.contract",
        0,
    )
    .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the scalar-local caller proof");
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_cpp_prepared_project(&rewritten, &import)
        .expect("the expanded scalar-local proof must reverify");
    let (session, _) = C0VerificationSession::new_cpp_prepared_project(&click_project, &import)
        .expect("retain the scalar-local verification environment");
    let next =
        cpp_prepared_project_tactic_source_position(&rewritten, &import, "relay_value.contract", 0)
            .unwrap();
    session
        .verify_at_project(&expanded, next.line, next.column)
        .expect("retained audit session must accept the expanded local proof");

    let false_contract = SCALAR_LOCAL_SIDECAR.replace(
        "ensures result == value[0] + 1;",
        "ensures result == value[0] + 2;",
    );
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_cpp_prepared_project(&false_project, &import)
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
    assert_eq!(import.export().schema, 9);
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
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("verify pointer load/store and reference address through shared rules");
    assert_eq!(verified.len(), 6);

    let execute = cpp_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "bump_reference.contract",
        0,
    )
    .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the pointer caller proof");
    verify_cpp_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded pointer proof must reverify");

    let missing_ownership = POINTER_SIDECAR.replacen("    owns pointer[0..1];\n", "", 1);
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_ownership_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_cpp_prepared_project(&missing_ownership_project, &import)
        .expect_err("dereferencing without memory authority must not verify");

    let false_contract = POINTER_SIDECAR.replace(
        "ensures value[0] == old(value[0]) + 1;",
        "ensures value[0] == old(value[0]) + 2;",
    );
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_cpp_prepared_project(&false_project, &import)
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
    assert_eq!(import.export().schema, 9);
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
            if matches!(pointee.as_ref(), CppType::Record { name, declaration_id }
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
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("verify field access and the loaded pointer through shared memory rules");
    assert_eq!(verified.len(), 7);

    let execute = cpp_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "stage_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the record execution proof");
    verify_cpp_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded record proof must reverify");

    let missing_ownership = STRUCT_MEMBER_SIDECAR.replace("    owns state->pointer;\n", "");
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_cpp_prepared_project(&missing_project, &import)
        .expect_err("writing a field without its memory authority must not verify");

    let false_contract =
        STRUCT_MEMBER_SIDECAR.replace("ensures value[0] == 7;", "ensures value[0] == 8;");
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_cpp_prepared_project(&false_project, &import)
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
    assert_eq!(import.export().schema, 9);
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
        CppType::Record { declaration_id, name }
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
    let verified = verify_cpp_prepared_project(&click_project, &import)
        .expect("verify local aggregate initialization and later field reads");
    assert_eq!(verified.len(), 3);

    let execute = cpp_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "stage_restore.contract",
        0,
    )
    .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the local aggregate execution proof");
    verify_cpp_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded local aggregate proof must reverify");

    let missing_ownership = LOCAL_AGGREGATE_SIDECAR.replace("    owns value[0..1];\n", "");
    fs::write(&sidecar, &missing_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_ownership).unwrap();
    verify_cpp_prepared_project(&missing_project, &import)
        .expect_err("the initializer and later pointer write require input memory authority");

    let false_contract =
        LOCAL_AGGREGATE_SIDECAR.replace("ensures result == old(value[0]);", "ensures result == 7;");
    fs::write(&sidecar, &false_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_contract).unwrap();
    verify_cpp_prepared_project(&false_project, &import)
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
    assert_eq!(import.export().schema, 9);
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
    assert!(contains_aggregate_construction_begin(
        lowered.kernel_function().body(),
        "state"
    ));
    assert!(contains_call(
        lowered.kernel_function().body(),
        "RestoreState_constructor"
    ));
    assert_eq!(lowered.reachable_kernel_functions().len(), 1);
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
    verify_cpp_prepared_project(&click_project, &import)
        .expect("verify the constructor body and its implicit local invocation modularly");

    let execute =
        cpp_prepared_project_tactic_source_position(&click_project, &import, "capture.contract", 0)
            .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the caller proof across construction");
    verify_cpp_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("the expanded constructor caller proof must reverify");

    let missing_field_ownership = CONSTRUCTOR_LOCAL_SIDECAR.replace("    owns self->saved;\n", "");
    fs::write(&sidecar, &missing_field_ownership).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_field_ownership).unwrap();
    verify_cpp_prepared_project(&missing_project, &import)
        .expect_err("constructor member initialization requires field authority");

    let false_constructor_contract = CONSTRUCTOR_LOCAL_SIDECAR.replace(
        "ensures self->saved == old(slot[0]);",
        "ensures self->saved == old(slot[0]) + 1;",
    );
    fs::write(&sidecar, &false_constructor_contract).unwrap();
    let false_project = read_click_project(&sidecar, &false_constructor_contract).unwrap();
    verify_cpp_prepared_project(&false_project, &import)
        .expect_err("a false constructor field effect must be rejected");
}

#[test]
fn terminal_return_captures_value_before_checked_destructor_cleanup() {
    let project = Project::terminal_destructor();
    let sidecar = project.directory.join("demo.click");
    fs::write(&sidecar, TERMINAL_DESTRUCTOR_SIDECAR).unwrap();
    refresh_import(&project.config()).expect("export constructor and terminal destructor cleanup");
    fs::remove_file(&project.exporter).expect("make the frontend unavailable after refresh");

    let import = load_import(&project.config()).expect("load the cleanup artifact offline");
    assert_eq!(import.export().schema, 9);
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
    verify_cpp_prepared_project(&click_project, &import)
        .expect("verify captured result and restored caller memory");

    let execute =
        cpp_prepared_project_tactic_source_position(&click_project, &import, "capture.contract", 0)
            .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .expect("expand the proof across terminal cleanup");
    verify_cpp_prepared_project(&click_project.with_entry_source(expanded), &import)
        .expect("expanded terminal-cleanup proof must reverify");

    let missing_destructor = TERMINAL_DESTRUCTOR_SIDECAR.replace(
        "void RestoreState_destructor(struct RestoreState* self) {\n    requires separate(memory(object(self)), memory(self->pointer[0..1]));\n    owns self->pointer;\n    owns self->saved;\n    owns self->pointer[0..1];\n    ensures self->pointer == old(self->pointer);\n    ensures self->saved == old(self->saved);\n    ensures self->pointer[0] == old(self->saved);\n} by {\n    execute();\n    simp();\n}\n\n",
        "",
    );
    fs::write(&sidecar, &missing_destructor).unwrap();
    let missing_project = read_click_project(&sidecar, &missing_destructor).unwrap();
    verify_cpp_prepared_project(&missing_project, &import)
        .expect_err("implicit cleanup requires a checked destructor contract");

    let false_destructor = TERMINAL_DESTRUCTOR_SIDECAR.replace(
        "ensures self->pointer[0] == old(self->saved);",
        "ensures self->pointer[0] == old(self->saved) + 1;",
    );
    fs::write(&sidecar, &false_destructor).unwrap();
    let false_project = read_click_project(&sidecar, &false_destructor).unwrap();
    verify_cpp_prepared_project(&false_project, &import)
        .expect_err("a false destructor restore effect must be rejected");

    let wrong_capture = TERMINAL_DESTRUCTOR_SIDECAR
        .replace("ensures result == 7;", "ensures result == old(value[0]);");
    fs::write(&sidecar, &wrong_capture).unwrap();
    let wrong_project = read_click_project(&sidecar, &wrong_capture).unwrap();
    verify_cpp_prepared_project(&wrong_project, &import)
        .expect_err("the return value must be captured before destruction");
}

#[test]
fn constructor_local_rejects_implicit_throwing_partial_and_reordered_forms() {
    let project = Project::constructor_local();
    for (source, expected) in [
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    RestoreState(int* slot) noexcept : pointer(slot), saved(*slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "public explicit non-default noexcept constructor",
        ),
        (
            "struct RestoreState {\n    int* pointer;\n    int saved;\n    explicit RestoreState(int* slot) : pointer(slot), saved(*slot) {}\n};\nint capture(int& value) noexcept { RestoreState state(&value); return state.saved; }\n",
            "public explicit non-default noexcept constructor",
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
                "if (value == 7) { return value; }\n    return value;",
            ),
            "branches with automatic destruction",
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
            "one object per function",
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
fn cpp_pointer_slice_rejects_arithmetic_null_multilevel_and_pointer_locals() {
    let project = Project::pointer();

    fs::write(
        project.source(),
        "int bump_reference(int* pointer) noexcept {\n    return *(pointer + 1);\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:2"), "{error}");
    assert!(error.contains("pointer arithmetic"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int read_pointer(int* pointer) noexcept { return *pointer; }\n\nint bump_reference(int& value) noexcept {\n    int result = read_pointer(nullptr);\n    return result;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:4"), "{error}");
    assert!(error.contains("unsupported implicit conversion"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int bump_reference(int& value) noexcept {\n    int* pointer = &value;\n    return *pointer;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("bump_reference.cpp:2"), "{error}");
    assert!(error.contains("must resolve to mutable int"), "{error}");
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
fn cpp_record_slice_rejects_methods_bitfields_inheritance_and_multiple_types() {
    let project = Project::struct_member();

    fs::write(
        project.source(),
        "struct RestoreState {\n    int saved;\n    int read() noexcept { return saved; }\n};\n\nint stage_restore(RestoreState& state, int& value) noexcept {\n    return state.saved;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("stage_restore.cpp:3"), "{error}");
    assert!(error.contains("ordinary methods"), "{error}");
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
    assert!(error.contains("have no bases"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "struct First { int value; };\nstruct Second { int value; };\n\nint stage_restore(First& first, Second& second) noexcept {\n    first.value = second.value;\n    return first.value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("stage_restore.cpp:2"), "{error}");
    assert!(error.contains("exactly one record type"), "{error}");
    assert!(!project.artifact().exists());
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

    let sites = cpp_prepared_project_smart_tactic_source_sites(&click_project, &import).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| site.tactic_name.as_str())
            .collect::<Vec<_>>(),
        vec!["execute", "simp"]
    );
    let execute = cpp_prepared_project_tactic_source_position(
        &click_project,
        &import,
        "increment.contract",
        0,
    )
    .unwrap();
    let expanded = expand_cpp_prepared_project_tactic_source_at(
        &click_project,
        &import,
        execute.line,
        execute.column,
    )
    .unwrap();
    assert_ne!(expanded, click_source);
    let rewritten = click_project.with_entry_source(expanded.clone());
    verify_cpp_prepared_project(&rewritten, &import).expect("expanded proof must reverify");

    let (session, _) = C0VerificationSession::new_cpp_prepared_project(&click_project, &import)
        .expect("start the retained audit session");
    let next =
        cpp_prepared_project_tactic_source_position(&rewritten, &import, "increment.contract", 0)
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
    let error = verify_cpp_prepared_project(&click_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("prepared C++ import logical source must exactly match"),
        "{}",
        error.message()
    );

    let wrong_signature = SIDECAR.replace("int32* value", "uint32* value");
    fs::write(&sidecar, &wrong_signature).unwrap();
    let click_project = read_click_project(&sidecar, &wrong_signature).unwrap();
    let error = verify_cpp_prepared_project(&click_project, &import).unwrap_err();
    assert!(
        error
            .message()
            .contains("signature mismatch for `increment` parameter 1"),
        "{}",
        error.message()
    );
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
    assert_eq!(function.parameters()[0].name(), "value");
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
                } if pointer == "value"
                    && matches!(
                        left.as_ref(),
                        CExpression::TypedLoad {
                            pointer,
                            value_type: CType::Int32,
                            volatile: false,
                            ..
                        } if matches!(pointer.as_ref(), CExpression::Variable(name) if name == "value")
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
                }) if matches!(pointer.as_ref(), CExpression::Variable(name) if name == "value")
            )
    ));

    let pointer = Pointer {
        block: "cpp-reference".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources =
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )));
    let arguments = vec![c_typed_pointer_value(pointer.clone(), CType::Int32Pointer)];
    let state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(41)))
        .with_resource_context(resources.clone());
    let expected_state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(42)))
        .with_resource_context(resources.clone());
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
            state,
            function: function.clone(),
            arguments: arguments.clone(),
            outcome: CFunctionOutcome::Return {
                value: int32(42),
                state: expected_state,
            },
        }
    );

    let max_state = CState::new()
        .with_memory(CMemory::new().store(pointer, int32(i32::MAX as u32)))
        .with_resource_context(resources);
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
            state: max_state,
            function: function.clone(),
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
    assert!(
        error.contains("standard-layout and trivially-copyable"),
        "{error}"
    );
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
fn cpp_scalar_locals_reject_uninitialized_reference_and_nested_declarations() {
    let project = Project::scalar_local();
    fs::write(
        project.source(),
        "int relay_value(int& value) noexcept {\n    int captured;\n    return value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("relay_value.cpp:2"), "{error}");
    assert!(error.contains("requires an initializer"), "{error}");
    assert!(!project.artifact().exists());

    fs::write(
        project.source(),
        "int relay_value(int& value) noexcept {\n    int& captured = value;\n    return captured;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("relay_value.cpp:2"), "{error}");
    assert!(error.contains("must resolve to mutable int"), "{error}");
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
    assert!(error.contains("explicit noexcept function"), "{error}");
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
}

#[test]
fn exporter_path_is_not_needed_by_offline_load() {
    let project = Project::new();
    refresh_import(&project.config()).unwrap();
    fs::remove_file(&project.exporter).unwrap();
    assert!(!Path::new(&project.exporter).exists());
    load_import(&project.config()).unwrap();
}
