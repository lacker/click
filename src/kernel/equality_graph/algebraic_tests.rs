use super::*;
use std::collections::BTreeMap;
use std::sync::Arc;

pub(super) fn model_type(name: &str, field: AlgebraicValueType) -> AlgebraicType {
    let nominal = AlgebraicValueType::Algebraic {
        name: name.into(),
        arguments: vec![],
    };
    let variants: Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Empty".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Node".into(),
            fields: vec![field],
        },
    ]
    .into();
    AlgebraicType {
        rigid: false,
        name: name.into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(nominal, variants)]))),
    }
}
pub(super) fn variable(ty: &AlgebraicType, id: u64) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(id)),
    }
}
fn constructor(ty: &AlgebraicType, variant: &str, fields: Vec<AlgebraicValue>) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: variant.into(),
            fields,
        },
    }
}
fn eq(a: &AlgebraicTerm, b: &AlgebraicTerm) -> Proposition {
    Proposition::Equal(Term::Algebraic(a.clone()), Term::Algebraic(b.clone()))
}
fn condition(a: &AlgebraicTerm, b: &AlgebraicTerm, truth: bool) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::AlgebraicEqual(Box::new(a.clone()), Box::new(b.clone())),
        truth,
    )
}
fn scalar(id: u64) -> AlgebraicValue {
    AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::Variable(Variable(id))))
}

#[test]
fn algebraic_closure_connects_checked_aliases_in_both_orientations() {
    let ty = model_type("Model", AlgebraicValueType::Program(ProgramType::Int32));
    let (a, b, c) = (variable(&ty, 1), variable(&ty, 2), variable(&ty, 3));
    let empty = constructor(&ty, "Empty", vec![]);
    let node = constructor(&ty, "Node", vec![scalar(4)]);
    for ctor in [&empty, &node] {
        for reverse in [false, true] {
            let alias = if reverse { eq(&b, &a) } else { eq(&a, &b) };
            let context = PureFactContext::new()
                .assume_proposition(alias)
                .assume_proposition(condition(&c, &b, true))
                .assume_proposition(eq(&c, ctor));
            assert!(context.contains_known(&eq(&a, ctor)));
            assert!(context.contains_known(&condition(ctor, &a, true)));
            let mut derived = context.equality_graph.input_root();
            assert!(derived.append_inputs_from(&context.equality_graph));
            assert!(derived.are_algebraic_equal(&a, ctor));
        }
    }
}

#[test]
fn algebraic_closure_preserves_types_constructors_payloads_and_argument_order() {
    let ty = model_type("Model", AlgebraicValueType::Program(ProgramType::Int32));
    let same = model_type("Model", AlgebraicValueType::Program(ProgramType::Int32));
    let other = model_type("Other", AlgebraicValueType::Program(ProgramType::Int32));
    let changed = model_type("Model", AlgebraicValueType::Program(ProgramType::UInt32));
    let a = variable(&ty, 10);
    let node = constructor(&ty, "Node", vec![scalar(11)]);
    let mut graph = EqualityGraph::default();
    graph.add_algebraic_equality(&a, &node);
    assert!(graph.are_algebraic_equal(&variable(&same, 10), &node));
    assert!(!graph.are_algebraic_equal(&variable(&other, 10), &node));
    assert!(!graph.are_algebraic_equal(&variable(&changed, 10), &node));
    assert!(!graph.are_algebraic_equal(&a, &constructor(&ty, "Empty", vec![])));
    assert!(!graph.are_algebraic_equal(&a, &constructor(&ty, "Node", vec![scalar(12)])));
    assert!(!graph.add_algebraic_equality(&variable(&other, 10), &a));
    assert!(!graph.add_algebraic_equality(&a, &constructor(&ty, "Node", vec![])));
    let f = |name: &str, args: Vec<PureFunctionArgument>| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::PureFunctionApplication {
            name: name.into(),
            arguments: args,
        },
    };
    let args = |x, y| {
        vec![
            PureFunctionArgument::Algebraic(x),
            PureFunctionArgument::Algebraic(y),
        ]
    };
    let b = variable(&ty, 13);
    assert!(!graph.are_algebraic_equal(
        &f("f", args(a.clone(), b.clone())),
        &f("f", args(b.clone(), a.clone()))
    ));
    assert!(!graph.are_algebraic_equal(
        &f("f", args(a.clone(), b.clone())),
        &f("g", args(a.clone(), b.clone()))
    ));
    graph.add_algebraic_equality(
        &f("f", args(a.clone(), b.clone())),
        &f("f", args(b.clone(), a.clone())),
    );
    assert!(!graph.are_algebraic_equal(&a, &b)); // no function injectivity
}

#[test]
fn algebraic_closure_propagates_late_model_and_scalar_merges_through_calls() {
    let ty = model_type("Model", AlgebraicValueType::Program(ProgramType::Int32));
    let (a, b) = (variable(&ty, 20), variable(&ty, 21));
    let call = |v| MachineTerm::ClickFunctionApplication {
        name: "model_size".into(),
        arguments: vec![PureFunctionArgument::Algebraic(v)],
    };
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_int32_equal(&call(a.clone()), &call(b.clone())));
    graph.add_algebraic_equality(&a, &b);
    assert!(graph.are_int32_equal(&call(a), &call(b)));
    let lhs = constructor(&ty, "Node", vec![scalar(22)]);
    let rhs = constructor(&ty, "Node", vec![scalar(23)]);
    assert!(!graph.are_algebraic_equal(&lhs, &rhs));
    graph.add_int32_equality(
        &MachineTerm::Variable(Variable(22)),
        &MachineTerm::Variable(Variable(23)),
    );
    assert!(graph.are_algebraic_equal(&lhs, &rhs));
}

#[test]
fn algebraic_closure_keeps_branch_scope() {
    let ty = model_type("Model", AlgebraicValueType::Program(ProgramType::Int32));
    let (a, b) = (variable(&ty, 30), variable(&ty, 31));
    let empty = constructor(&ty, "Empty", vec![]);
    let edge = eq(&a, &b);
    let ctor = eq(&b, &empty);
    let base = PureFactContext::new().assume_proposition(edge.clone());
    let branch = base.clone().assume_proposition(ctor.clone());
    assert!(!base.contains_known(&eq(&a, &empty)));
    assert!(branch.contains_known(&eq(&a, &empty)));
    assert!(
        !PureFactContext::new()
            .assume_proposition(ctor)
            .contains_known(&eq(&a, &empty))
    );
    assert!(
        !branch
            .restricted_to_facts(&[], std::slice::from_ref(&edge))
            .contains_known(&eq(&a, &empty))
    );
    let negative = base.assume_proposition(condition(&b, &empty, false));
    assert!(!negative.contains_known(&eq(&a, &empty)));
    assert!(negative.contains_known(&condition(&a, &empty, false)));
    assert!(!negative.contains_known(&condition(&a, &empty, true)));
}

#[test]
fn algebraic_closure_generic_arguments_and_constructor_field_order_remain_typed() {
    let mut ty = model_type("Pair", AlgebraicValueType::Program(ProgramType::Int32));
    ty.arguments = vec![AlgebraicValueType::Program(ProgramType::Int32)];
    ty.variants = vec![AlgebraicVariantType {
        name: "Node".into(),
        fields: vec![AlgebraicValueType::Program(ProgramType::Int32); 2],
    }]
    .into();
    ty.schemas = Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
        ty.value_type(),
        ty.variants.clone(),
    )])));
    let mut other = ty.clone();
    other.arguments = vec![AlgebraicValueType::Program(ProgramType::UInt32)];
    other.schemas = Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
        other.value_type(),
        other.variants.clone(),
    )])));
    let mut graph = EqualityGraph::default();
    let a = constructor(&ty, "Node", vec![scalar(60), scalar(61)]);
    let b = constructor(&ty, "Node", vec![scalar(61), scalar(60)]);
    assert!(!graph.are_algebraic_equal(&a, &b));
    assert!(!graph.are_algebraic_equal(
        &a,
        &constructor(&other, "Node", vec![scalar(60), scalar(61)])
    ));
    graph.add_algebraic_equality(&variable(&ty, 62), &a);
    assert!(!graph.are_algebraic_equal(&variable(&other, 62), &a));
}

#[test]
fn algebraic_closure_pointer_payloads_require_full_value_equality() {
    let ty = model_type(
        "PointerModel",
        AlgebraicValueType::Program(ProgramType::Int32Pointer),
    );
    let pointer = |name: &str| Pointer {
        block: name.into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let node = |p: Pointer| {
        constructor(
            &ty,
            "Node",
            vec![AlgebraicValue::Program(ProgramValue::Pointer(
                PointerValue::new(p, ProgramType::Int32Pointer),
            ))],
        )
    };
    let mut graph = EqualityGraph::default();
    graph.add_equality(&pointer("a"), &pointer("b"));
    assert!(!graph.are_algebraic_equal(&node(pointer("a")), &node(pointer("b"))));
    graph.add_pointer_value_equality(
        &PointerValue::new(pointer("a"), ProgramType::Int32Pointer),
        &PointerValue::new(pointer("b"), ProgramType::Int32Pointer),
    );
    assert!(graph.are_algebraic_equal(&node(pointer("a")), &node(pointer("b"))));
}

#[test]
fn algebraic_closure_retains_each_schema_allocation_behind_a_memo_key() {
    let first = model_type("Model", AlgebraicValueType::Program(ProgramType::Int32));
    let second = model_type("Model", AlgebraicValueType::Program(ProgramType::Int32));
    assert!(!Arc::ptr_eq(&first.variants, &second.variants));
    let weak = Arc::downgrade(&second.variants);
    let graph = EqualityGraph::default();
    assert!(graph.are_algebraic_equal(&variable(&first, 70), &variable(&second, 70)));
    drop(second);
    // Interning equal types may retain only the first allocation. The memo
    // must independently retain the second so its address cannot be reused
    // for a different schema while the key remains live.
    assert!(weak.upgrade().is_some());
    drop(graph);
    assert!(weak.upgrade().is_none());
}

#[test]
fn scalar_conflicts_follow_model_congruence() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type(
        "ConflictModel",
        AlgebraicValueType::Program(ProgramType::Int32),
    );
    let (a, b) = (variable(&ty, 900), variable(&ty, 901));
    let getter = |v| MachineTerm::ClickFunctionApplication {
        name: "pending".into(),
        arguments: vec![PureFunctionArgument::Algebraic(v)],
    };
    let value = |v, n| {
        Proposition::ConditionIs(
            ConditionTerm::equal(getter(v), MachineTerm::constant(n)),
            true,
        )
    };
    let first = value(a.clone(), 1);
    let second = value(b.clone(), 0);
    let edge = eq(&a, &b);
    let base = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second);
    assert!(!base.equality_graph.has_scalar_constant_conflict());
    assert!(!base.is_inconsistent());
    let child = base.clone().assume_proposition(edge.clone());
    assert!(child.contains_known(&value(a.clone(), 0)));
    assert!(child.equality_graph.has_scalar_constant_conflict());
    assert!(child.is_inconsistent());
    assert!(child.contains_known(&Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true
    )));
    assert!(!base.equality_graph.has_scalar_constant_conflict());
    for weakened in [
        PureFactContext::new()
            .assume_proposition(first)
            .assume_proposition(edge.clone()),
        child.restricted_to_facts(&[], std::slice::from_ref(&edge)),
    ] {
        assert!(!weakened.equality_graph.has_scalar_constant_conflict());
        assert!(!weakened.is_inconsistent());
    }
}

#[test]
fn scalar_constant_conflicts_preserve_machine_widths() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut graph = EqualityGraph::default();
    let x = MachineTerm::Variable(Variable(700));
    graph.add_int32_equality(&x, &MachineTerm::constant(0));
    graph.add_uint64_equality(&x, &MachineTerm::uint64_constant(1));
    assert!(!graph.has_scalar_constant_conflict());
    graph.add_uint64_equality(&x, &MachineTerm::uint64_constant(0));
    assert!(graph.has_scalar_constant_conflict());
    let mut graph = EqualityGraph::default();
    graph.add_int32_equality(&MachineTerm::constant(0), &MachineTerm::constant(1));
    assert!(graph.has_scalar_constant_conflict());
}

#[test]
fn scalar_read_conflicts_require_the_same_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer {
        block: "cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = Memory::new().with_block("cell", 4).store(
        p.clone(),
        ProgramValue::Int32(MachineTerm::Variable(Variable(500))),
    );
    let after = before.clone().store(
        p.clone(),
        ProgramValue::Int32(MachineTerm::Variable(Variable(501))),
    );
    let memory = crate::kernel::intern_memory(before);
    let changed = crate::kernel::intern_memory(after);
    let read = |memory: crate::kernel::SharedMemory| {
        MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &p,
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        ))
    };
    let value = |term, n| {
        Proposition::ConditionIs(ConditionTerm::equal(term, MachineTerm::constant(n)), true)
    };
    for (right_memory, conflict) in [(memory.clone(), true), (changed, false)] {
        let context = PureFactContext::new()
            .assume_proposition(value(read(memory.clone()), 0))
            .assume_proposition(value(read(right_memory), 1));
        assert_eq!(
            context.equality_graph.has_scalar_constant_conflict(),
            conflict
        );
        assert_eq!(context.is_inconsistent(), conflict);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/equality_graph/algebraic_tests.rs");
}

#[test]
fn model_constructor_lookup_uses_shared_classes_and_scoped_evidence() {
    let ty = model_type(
        "ConstructorLookup",
        AlgebraicValueType::Program(ProgramType::Int32),
    );
    let (a, b, c) = (variable(&ty, 71), variable(&ty, 72), variable(&ty, 73));
    let ctor = constructor(&ty, "Node", vec![scalar(17)]);
    for reverse in [false, true] {
        let base = PureFactContext::new().assume_proposition(eq(&a, &b));
        let joined = if reverse {
            base.clone()
                .assume_proposition(eq(&c, &ctor))
                .assume_proposition(eq(&b, &c))
        } else {
            base.clone()
                .assume_proposition(eq(&b, &c))
                .assume_proposition(eq(&c, &ctor))
        };
        assert_eq!(joined.known_algebraic_constructor(&a), Some(ctor.clone()));
        assert_eq!(base.known_algebraic_constructor(&a), None);
        let unjoined = base.clone().assume_proposition(eq(&c, &ctor));
        assert_eq!(unjoined.known_algebraic_constructor(&a), None);
        assert_eq!(unjoined.known_algebraic_constructor(&c), Some(ctor.clone()));
        assert_eq!(joined.known_algebraic_constructor(&a), Some(ctor.clone()));
    }
    let other_ty = model_type(
        "OtherConstructorLookup",
        AlgebraicValueType::Program(ProgramType::Int32),
    );
    let other = variable(&other_ty, 71);
    let joined = PureFactContext::new().assume_proposition(eq(&a, &ctor));
    assert_eq!(joined.known_algebraic_constructor(&other), None);
}

#[test]
fn model_constructor_lookup_prefers_a_stated_constructor_on_an_infeasible_path() {
    // `__rb_insert` matches `c.model` as `Left` on a path where `c.model` is
    // also derived to be `Top`. The class keeps one witness, so the stated
    // constructor must win whichever reached the class first.
    let ty = model_type(
        "StatedConstructor",
        AlgebraicValueType::Program(ProgramType::Int32),
    );
    let (model, alias) = (variable(&ty, 81), variable(&ty, 82));
    let empty = constructor(&ty, "Empty", vec![]);
    let node = constructor(&ty, "Node", vec![scalar(18)]);
    for derived_first in [false, true] {
        let base = PureFactContext::new().assume_proposition(eq(&model, &alias));
        let joined = if derived_first {
            base.assume_proposition(eq(&alias, &empty))
                .assume_proposition(eq(&model, &node))
        } else {
            base.assume_proposition(eq(&model, &node))
                .assume_proposition(eq(&alias, &empty))
        };
        assert_eq!(
            joined.known_algebraic_constructor(&model),
            Some(node.clone())
        );
        assert_eq!(
            joined.known_algebraic_constructor(&alias),
            Some(empty.clone())
        );
    }
}

#[test]
fn constructor_classes_join_fields_and_refute_distinct_variants() {
    let _session = crate::kernel::VerificationSession::enter();
    let ty = model_type("Injective", AlgebraicValueType::Program(ProgramType::Int32));
    let (model, alias) = (variable(&ty, 90), variable(&ty, 91));
    let first = eq(&model, &constructor(&ty, "Node", vec![scalar(92)]));
    let second = eq(&constructor(&ty, "Node", vec![scalar(93)]), &alias);
    let fields = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::Variable(Variable(92)),
            MachineTerm::Variable(Variable(93)),
        ),
        true,
    );
    let edge = eq(&model, &alias);
    let base = PureFactContext::new()
        .assume_proposition(first.clone())
        .assume_proposition(second.clone());
    assert!(!base.contains_known(&fields));
    let joined = base.clone().assume_proposition(edge.clone());
    assert!(joined.contains_known(&fields));
    assert!(!joined.equality_graph.has_scalar_constant_conflict());
    assert!(!base.contains_known(&fields));
    for weakened in [
        PureFactContext::new()
            .assume_proposition(second)
            .assume_proposition(edge.clone()),
        joined.restricted_to_facts(&[], &[first.clone(), edge.clone()]),
    ] {
        assert!(!weakened.contains_known(&fields));
    }

    let empty = eq(&alias, &constructor(&ty, "Empty", vec![]));
    let held = PureFactContext::new().assume_proposition(first);
    let refuted = held
        .clone()
        .assume_proposition(empty.clone())
        .assume_proposition(edge.clone());
    assert!(refuted.equality_graph.has_scalar_constant_conflict());
    assert!(refuted.is_inconsistent());
    for weakened in [
        held.clone().assume_proposition(empty),
        held.assume_proposition(edge),
    ] {
        assert!(!weakened.equality_graph.has_scalar_constant_conflict());
    }
}

/// A field holding a value of an abstract type is that value's term: two
/// constructors whose abstract payloads are equal are equal, and unequal
/// payloads keep them apart.
#[test]
fn algebraic_closure_abstract_payloads_follow_their_terms() {
    let parameter = AlgebraicType::parameter("T".into());
    let ty = model_type(
        "Maybe",
        AlgebraicValueType::Program(ProgramType::Parameter(TypeParameterName::of(&parameter))),
    );
    let payload =
        |id| AlgebraicValue::Program(ProgramValue::Parameter(Box::new(variable(&parameter, id))));
    let some = |id| constructor(&ty, "Node", vec![payload(id)]);
    let mut graph = EqualityGraph::default();
    assert!(!graph.are_algebraic_equal(&some(70), &some(71)));
    graph.add_algebraic_equality(&variable(&parameter, 70), &variable(&parameter, 71));
    assert!(graph.are_algebraic_equal(&some(70), &some(71)));
    assert!(!graph.are_algebraic_equal(&some(70), &some(72)));
}
