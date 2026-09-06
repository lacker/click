use super::prelude::*;

fn checked_memory_load_equality(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    checked_atomic_load_equality(
        &Bitvector32Term::MemoryLoad(intern_c_memory_ref(left), Box::new(pointer.clone())),
        &Bitvector32Term::MemoryLoad(intern_c_memory_ref(right), Box::new(pointer.clone())),
        assumptions,
    )
}

mod canonicalization_tests;
mod contract_execution_tests;
mod execution_tests;
mod expression_tests;
mod fact_publication_tests;
mod memory_reasoning_tests;
mod proof_reasoning_tests;
mod resource_tests;

/// Certifies a contract from the kernel's own checked executions of the
/// function, one per resource-guard case, the way the surface certifies a
/// proof's artifacts: certification itself never executes a body.
#[allow(clippy::too_many_arguments)]
fn certify_contract_with_kernel_artifacts(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    derived_entry_facts: Vec<Proposition>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
) -> CFunctionContractExecution {
    let assume_all = |facts: &[Proposition]| {
        facts
            .iter()
            .fold(PureFactContext::new(), |assumptions, fact| {
                assumptions.assume_proposition(fact.clone())
            })
    };
    let cases = crate::kernel::api::contract_certification::contract_resource_condition_cases(
        &state,
        &function,
        &arguments,
        &assume_all(&derived_entry_facts),
    )
    .unwrap_or_else(|| vec![Vec::new()]);
    let artifacts = cases
        .iter()
        .map(|case_facts| {
            let mut facts = derived_entry_facts.clone();
            facts.extend(case_facts.iter().cloned());
            prove_checked_c_function_execution_with_environment(
                state.clone(),
                function.clone(),
                arguments.clone(),
                assume_all(&facts),
                environment.clone(),
                execution_semantics,
                mode,
            )
        })
        .collect::<Vec<_>>();
    prove_c_function_contract_execution_paths_with_checked_artifacts(
        state,
        function,
        arguments,
        derived_entry_facts,
        environment,
        execution_semantics,
        mode,
        &artifacts,
    )
}

/// Contract certification calls no general prover: every proposition it
/// certifies is decided by an exact rule of its own, a completion match,
/// or a kind-specific bounded rule, never by handing the question to
/// `PureFactContext::proves`.
#[test]
fn contract_certification_calls_no_general_prover() {
    let needle = [".prov", "es("].concat();
    let sources = [
        "src/kernel/api/contract_certification.rs",
        "src/kernel/api/contract_certification/contract_claims.rs",
    ];
    let offenders = sources
        .iter()
        .filter(|relative| {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
            std::fs::read_to_string(path)
                .expect("certification source is readable")
                .contains(&needle)
        })
        .collect::<Vec<_>>();
    assert!(
        offenders.is_empty(),
        "contract certification hands a proposition to the general prover: {offenders:?}"
    );
}

/// Boundaries whose load equality is present in the recorded memory DAG must
/// not regain the ambient whole-context prover. Framed atomic transport still
/// uses that prover until its assumption-dependent hop has typed evidence.
#[test]
fn migrated_load_equality_consumers_use_recorded_dag_evidence() {
    let needle = ["c_memory_load", "_is_unchanged("].concat();
    let sources = [
        "src/kernel/api/contract_certification.rs",
        "src/kernel/api/contract_certification/contract_claims.rs",
        "src/kernel/loops.rs",
        "src/kernel/primitives/resource_algebra.rs",
        "src/kernel/proof/fact_reasoning.rs",
        "src/surface/proof.rs",
    ];
    let offenders = sources
        .iter()
        .filter(|relative| {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
            std::fs::read_to_string(path)
                .expect("load-equality consumer source is readable")
                .contains(&needle)
        })
        .collect::<Vec<_>>();
    assert!(
        offenders.is_empty(),
        "migrated load-equality consumer invokes the global prover: {offenders:?}"
    );
}

/// The kernel reads no environment variable: its behaviour is fixed, and
/// its test-only audits are switched on by the tests that run them. Every
/// A/B handle it once read kept a second code path alive.
#[test]
fn kernel_source_reads_no_environment_variable() {
    fn source_files(directory: &std::path::Path, files: &mut Vec<std::path::PathBuf>) {
        for entry in std::fs::read_dir(directory).expect("kernel source directory is readable") {
            let path = entry.expect("kernel source entry is readable").path();
            if path.is_dir() {
                source_files(&path, files);
            } else if path.extension().is_some_and(|extension| extension == "rs") {
                files.push(path);
            }
        }
    }
    let kernel = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/kernel");
    let mut files = Vec::new();
    source_files(&kernel, &mut files);
    assert!(files.len() > 20, "the kernel source tree was not found");
    let offenders = files
        .iter()
        .filter(|path| {
            let source = std::fs::read_to_string(path).expect("kernel source is readable");
            source.contains(&["env", "::var"].concat())
        })
        .map(|path| path.display().to_string())
        .collect::<Vec<_>>();
    assert!(
        offenders.is_empty(),
        "kernel sources read an environment variable: {offenders:?}"
    );
}

fn memory_range(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CMemoryRange {
    CMemoryRange::new(base, start.into(), end.into())
}

fn view_memory_fact(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::view_memory(memory_range(base, start, end))
}

fn own_memory_fact(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::own_memory(memory_range(base, start, end))
}

fn view_memory_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(view_memory_fact(base, start, end))
}

fn own_memory_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(own_memory_fact(base, start, end))
}

fn assert_checkable_derivation(assumptions: &PureFactContext, proposition: &Proposition) {
    let derivation = assumptions
        .derive_proposition(proposition)
        .expect("expected an explicit proposition derivation");
    assert_eq!(derivation.conclusion(), proposition);
    assert!(
        derivation.check(assumptions),
        "explicit proposition derivation must check"
    );
}

fn arc_pointer(offset: i64) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

mod memory_dag_tests;

mod heap_tests;
