use super::prelude::*;

mod canonicalization_tests;
mod contract_execution_tests;
mod execution_tests;
mod expression_tests;
mod fact_publication_tests;
mod memory_reasoning_tests;
mod proof_reasoning_tests;
mod resource_tests;

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
