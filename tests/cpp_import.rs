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
    CppBinaryOperator, CppExpression, CppStatement, CppType, load_import, lower_import,
    refresh_import,
};
use click::surface::{
    C0VerificationSession, VerifiedClaim, cpp_prepared_project_smart_tactic_source_sites,
    cpp_prepared_project_tactic_source_position, expand_cpp_prepared_project_tactic_source_at,
    verify_cpp_prepared_project,
};

const SOURCE: &str = include_str!("fixtures/cpp-verification/increment/increment.cpp");
const SIDECAR: &str = include_str!("fixtures/cpp-verification/increment/increment.click");

struct Project {
    directory: PathBuf,
    exporter: PathBuf,
}

impl Project {
    fn new() -> Self {
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
        fs::write(directory.join("increment.cpp"), SOURCE).unwrap();
        let project = Self {
            directory,
            exporter,
        };
        project.write_config("increment");
        project
    }

    fn config(&self) -> PathBuf {
        self.directory.join("demo.click.import.json")
    }

    fn artifact(&self) -> PathBuf {
        self.directory.join("increment.cpp.click-cpp.json")
    }

    fn lock(&self) -> PathBuf {
        self.directory.join("demo.click.import.json.lock")
    }

    fn source(&self) -> PathBuf {
        self.directory.join("increment.cpp")
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
            "source": "increment.cpp",
            "logical_source": "increment.cpp",
            "function": function,
            "artifact": "increment.cpp.click-cpp.json"
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
        "int increment(int* value) noexcept {\n    *value = *value + 1;\n    return *value;\n}\n",
    )
    .unwrap();
    let error = refresh_import(&project.config()).unwrap_err();
    assert!(error.contains("mutable int& parameter"), "{error}");
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
