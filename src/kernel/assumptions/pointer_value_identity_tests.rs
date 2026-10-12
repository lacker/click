use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;
use std::sync::Arc;

fn pointer_box(value: CValue) -> AlgebraicTerm {
    let name = "DesignatedPointerBox".to_string();
    let key = AlgebraicValueType::Algebraic {
        name: name.clone(),
        arguments: Vec::new(),
    };
    let variants: Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Pointer".into(),
        fields: vec![AlgebraicValueType::C(CType::Int32Pointer)],
    }]
    .into();
    AlgebraicTerm {
        algebraic_type: AlgebraicType {
            name,
            arguments: Vec::new(),
            variants: variants.clone(),
            schemas: Arc::new(AlgebraicSchemas::new(BTreeMap::from([(key, variants)]))),
            rigid: false,
        },
        node: AlgebraicTermNode::Constructor {
            variant: "Pointer".into(),
            fields: vec![AlgebraicValue::C(value)],
        },
    }
}

fn selected(member: &str, base: Pointer) -> CPointerValue {
    let root = Pointer {
        block: "local:pointer-value-pair".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    CPointerValue::new(root.offset_by_bytes(4), CType::Int32Pointer).with_designation(
        PointerDesignation::Object {
            root,
            path: vec![PointerDomainSelection::Member(member.into())].into(),
            base,
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::constant_i64(1).into(),
        },
    )
}

fn equality(left: &AlgebraicTerm, right: &AlgebraicTerm) -> Proposition {
    Proposition::Equal(
        Term::Algebraic(left.clone()),
        Term::Algebraic(right.clone()),
    )
}

fn instance(model: AlgebraicTerm) -> ResourceInstance {
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(model.algebraic_type.clone()),
    )])
    .unwrap();
    ResourceInstance::new(
        Variable(9_747_001),
        "pointer_model".into(),
        Vec::new().into(),
        schema,
        vec![AlgebraicValue::Algebraic(model)].into(),
    )
    .unwrap()
}

#[test]
fn pointer_value_identity_constructor_congruence_refuses_address_only_domain_changes() {
    let _session = crate::kernel::VerificationSession::enter();
    let root = Pointer {
        block: "local:pointer-value-pair".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first_past = selected("first", root.clone());
    let second = selected("second", root.offset_by_bytes(4));
    let legacy = CPointerValue::new(second.pointer().clone(), CType::Int32Pointer);
    let unresolved = legacy
        .clone()
        .with_designation(PointerDesignation::Unresolved(Variable(9_747_002)));
    let first_model = pointer_box(CValue::Pointer(first_past.clone()));
    for other in [second, legacy, unresolved] {
        let comparison = c_value_comparison_proposition(
            &CValue::Pointer(first_past.clone()),
            CComparisonOperator::Equal,
            &CValue::Pointer(other.clone()),
        )
        .unwrap();
        assert!(solve_builtin_prop(&comparison));
        let other_model = pointer_box(CValue::Pointer(other));
        let conclusion = equality(&first_model, &other_model);
        assert!(algebraic_constructor_field_equalities(&conclusion).is_none());
        let facts = PureFactContext::new().assume_proposition(comparison.clone());
        assert!(facts.derive_proposition(&conclusion).is_none());
        let forged = PropositionDerivation {
            conclusion: conclusion.clone(),
            rule: PropositionDerivationRule::AlgebraicConstructorCongruence {
                fields: vec![PropositionDerivation {
                    conclusion: comparison,
                    rule: PropositionDerivationRule::ContextFree,
                }],
            },
        };
        assert!(!forged.check(&facts));
        assert!(!solve_builtin_prop(&Proposition::Not(Box::new(
            conclusion.clone()
        ))));
        assert!(
            facts
                .derive_proposition(&Proposition::Not(Box::new(conclusion)))
                .is_none()
        );
        let actual = CResource::Instance(instance(first_model.clone()));
        let proposed = CResource::Instance(instance(other_model));
        assert!(
            !crate::kernel::memory_provenance::c_resources_directly_match(
                &actual, &proposed, &facts,
            )
        );
        let held = ResourceContext::new().unchecked_with_fact(CResourceFact::own(actual));
        assert!(!held.satisfies_fact(&CResourceFact::own(proposed), &facts));
    }
}

#[test]
fn pointer_value_identity_constructor_congruence_preserves_the_same_carried_domain() {
    let _session = crate::kernel::VerificationSession::enter();
    let root = Pointer {
        block: "local:pointer-value-pair".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = selected("first", root);
    let alternate = pointer
        .clone()
        .with_pointer(Pointer::symbolic(Variable(9_747_003)));
    let left = pointer_box(CValue::Pointer(pointer.clone()));
    let right = pointer_box(CValue::Pointer(alternate.clone()));
    let comparison = c_value_comparison_proposition(
        &CValue::Pointer(pointer),
        CComparisonOperator::Equal,
        &CValue::Pointer(alternate),
    )
    .unwrap();
    let conclusion = equality(&left, &right);
    let facts = PureFactContext::new().assume_proposition(comparison);
    let proof = facts.derive_proposition(&conclusion).unwrap();
    assert!(proof.check(&facts));
    assert!(!proof.check(&PureFactContext::new()));
    let facts = facts.assume_proposition(conclusion);
    let actual = CResource::Instance(instance(left));
    let proposed = CResource::Instance(instance(right));
    assert!(
        crate::kernel::memory_provenance::c_resources_directly_match(&actual, &proposed, &facts,)
    );
    let held = ResourceContext::new().unchecked_with_fact(CResourceFact::own(actual));
    assert!(held.satisfies_fact(&CResourceFact::own(proposed), &facts));
}
