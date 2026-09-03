use super::prelude::*;

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

/// Tests of behavior added by the memory DAG have nothing to assert when its
/// A/B switch disables that machinery.
fn skip_without_memory_dag() -> bool {
    memory_dag_disabled()
}

fn arc_pointer(offset: i64) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

mod memory_dag_tests;

mod heap_tests;
