use super::*;
use crate::kernel::VerificationSession;

fn call(name: &str, arguments: Vec<PureFunctionArgument>) -> Pointer {
    Pointer {
        block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: PointerOffsetTerm::Constant(0),
    }
}
fn word(id: u64) -> MachineTerm {
    MachineTerm::Variable(Variable(id))
}
fn argument(id: u64) -> PureFunctionArgument {
    PureFunctionArgument::Value(ProgramValue::Int32(word(id)))
}
fn pointer_argument(p: Pointer) -> PureFunctionArgument {
    PureFunctionArgument::Value(ProgramValue::Pointer(PointerValue::new(
        p,
        ProgramType::Int32Pointer,
    )))
}
fn equal_pointer_arguments(graph: &mut EqualityGraph, p: &Pointer, q: &Pointer) {
    graph.add_pointer_value_equality(
        &PointerValue::new(p.clone(), ProgramType::Int32Pointer),
        &PointerValue::new(q.clone(), ProgramType::Int32Pointer),
    );
}

fn equal(a: &Pointer, b: &Pointer) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::PointerEqual(Box::new(a.clone()), Box::new(b.clone())),
        true,
    )
}

#[test]
fn pointer_calls_follow_late_model_aliases_and_displaced_addresses() {
    let _session = VerificationSession::enter();
    let ty = super::algebraic_tests::model_type(
        "Handle",
        AlgebraicValueType::Program(ProgramType::Int32Pointer),
    );
    let a = super::algebraic_tests::variable(&ty, 10);
    let b = super::algebraic_tests::variable(&ty, 11);
    let f = |x| call("handle", vec![PureFunctionArgument::Algebraic(x)]);
    let (left, right) = (f(a.clone()), f(b.clone()));
    let mut graph = EqualityGraph::default();
    let shifted = |p: &Pointer| Pointer {
        block: p.block.clone(),
        offset: PointerOffsetTerm::Constant(8),
    };
    assert!(!graph.are_equal(&shifted(&left), &shifted(&right)));
    graph.add_algebraic_equality(&a, &b);
    assert!(graph.are_equal(&left, &right));
    assert!(graph.are_equal(&shifted(&left), &shifted(&right)));
    assert!(!graph.are_equal(&left, &shifted(&right)));
    assert!(!graph.are_equal(
        &left,
        &call("other", vec![PureFunctionArgument::Algebraic(b)])
    ));
}

#[test]
fn pointer_calls_keep_sorts_order_states_and_noninjectivity() {
    let _session = VerificationSession::enter();
    let mut graph = EqualityGraph::default();
    let p = Pointer::symbolic(Variable(30));
    let q = Pointer::symbolic(Variable(31));
    let memory = Memory::new().with_block(p.block.clone(), 4);
    let changed = memory
        .clone()
        .store(p.clone(), ProgramValue::Int32(word(32)));
    let array = |memory: &Memory, pointer, element_type| PureFunctionArgument::ArrayRef {
        memory: memory.clone(),
        pointer: ProgramValue::Pointer(PointerValue::new(pointer, ProgramType::Int32Pointer)),
        element_type,
    };
    let a = call(
        "select",
        vec![array(&memory, p.clone(), ProgramType::Int32)],
    );
    let b = call(
        "select",
        vec![array(&memory, q.clone(), ProgramType::Int32)],
    );
    assert!(!graph.are_equal(&a, &b));
    graph.add_equality(&p, &q);
    assert!(!graph.are_equal(&a, &b));
    equal_pointer_arguments(&mut graph, &p, &q);
    assert!(graph.are_equal(&a, &b));
    assert!(!graph.are_equal(
        &a,
        &call(
            "select",
            vec![array(&changed, q.clone(), ProgramType::Int32)]
        )
    ));
    assert!(!graph.are_equal(
        &a,
        &call("select", vec![array(&memory, q, ProgramType::UInt32)])
    ));
    let a = call("pair", vec![argument(33), argument(34)]);
    let b = call("pair", vec![argument(34), argument(33)]);
    assert!(!graph.are_equal(&a, &b));
    assert!(!graph.are_equal(
        &call("typed", vec![argument(33)]),
        &call(
            "typed",
            vec![PureFunctionArgument::Value(ProgramValue::UInt32(word(33)))]
        )
    ));
    assert!(!graph.are_equal(&a, &call("pair", vec![argument(33)])));
    graph.add_equality(&a, &b);
    assert!(!graph.are_int32_equal(&word(33), &word(34)));
}

#[test]
fn nested_pointer_calls_feed_scalar_calls_and_checked_reads() {
    let _session = VerificationSession::enter();
    let (p, q) = (
        Pointer::symbolic(Variable(40)),
        Pointer::symbolic(Variable(41)),
    );
    let build = |mut p: Pointer| {
        for _ in 0..12 {
            p = call("next", vec![pointer_argument(p)]);
        }
        p
    };
    let (a, b) = (build(p.clone()), build(q.clone()));
    let scalar = |p| MachineTerm::ClickFunctionApplication {
        name: "count".into(),
        arguments: vec![pointer_argument(p)],
    };
    let memory = intern_memory(Memory::new());
    let read = |p| {
        MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &p,
            LoadKind::Int32,
            4,
        ))
    };
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(&scalar(a.clone()), &scalar(b.clone())));
    assert!(!graph.are_int32_equal(&read(a.clone()), &read(b.clone())));
    graph.add_equality(&p, &q);
    assert!(!graph.are_equal(&a, &b));
    equal_pointer_arguments(&mut graph, &p, &q);
    assert!(graph.are_equal(&a, &b));
    assert!(graph.are_int32_equal(&scalar(a.clone()), &scalar(b.clone())));
    assert!(graph.are_int32_equal(&read(a), &read(b)));
}

#[test]
fn pointer_call_evidence_stays_scoped() {
    let _session = VerificationSession::enter();
    let (a, b) = (
        call("get", vec![argument(50)]),
        call("get", vec![argument(51)]),
    );
    let p = Pointer::symbolic(Variable(52));
    let premise = Proposition::ConditionIs(ConditionTerm::equal(word(50), word(51)), true);
    let held = equal(&p, &a);
    let goal = equal(&p, &b);
    let base = PureFactContext::new().assume_proposition(held.clone());
    assert!(!base.contains_known(&goal));
    let child = base.clone().assume_proposition(premise.clone());
    assert!(child.contains_known(&goal));
    assert!(!base.contains_known(&goal));
    assert!(
        !PureFactContext::new()
            .assume_proposition(premise)
            .contains_known(&goal)
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/pointer_call_tests.rs");
}

#[test]
fn pointer_call_address_equality_does_not_merge_result_domains() {
    let _session = VerificationSession::enter();
    let a = call("left", vec![argument(61)]);
    let b = call("right", vec![argument(61)]);
    let left = PointerValue::new(a.clone(), ProgramType::Int32Pointer);
    let right = PointerValue::new(b.clone(), ProgramType::Int32Pointer);
    let context = PureFactContext::new().assume_proposition(equal(&a, &b));
    assert!(!context.pointer_designations_match(&left, &right));
    let complete = context.clone().assume_condition(
        ConditionTerm::pointer_value_equal(left.clone(), right.clone()),
        true,
    );
    assert!(complete.pointer_designations_match(&left, &right));
    assert!(!context.pointer_designations_match(&left, &right));
}
