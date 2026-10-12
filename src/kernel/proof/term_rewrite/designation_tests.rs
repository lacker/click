use super::*;
use std::hash::{Hash, Hasher};

fn object(root: Pointer, member: &str, count: IntegerTerm) -> PointerDesignation {
    PointerDesignation::Object {
        root: root.clone(),
        path: vec![PointerDomainSelection::Member(member.into())].into(),
        base: root,
        element_type: CType::Int32,
        stride: 4,
        count: count.into(),
    }
}

fn value(pointer: Pointer, designation: PointerDesignation) -> CPointerValue {
    CPointerValue::new(pointer, CType::Int32Pointer).with_designation(designation)
}

#[test]
fn loaded_designation_retains_exact_origin_through_rewrites_and_casts() {
    let _session = VerificationSession::enter();
    let variable = Variable(410_070);
    let cell = Pointer::symbolic(variable);
    let snapshot = intern_c_memory(CMemory::new());
    let origin = PointerLoadIdentity::new(snapshot.clone(), cell.clone());
    let input = value(cell.clone(), PointerDesignation::Loaded(origin.clone()));
    assert_eq!(
        origin,
        PointerLoadIdentity::new(snapshot.clone(), cell.clone())
    );
    assert_eq!(
        origin.id(),
        Pointer::loaded_value(&snapshot, &cell)
            .as_loaded_value()
            .unwrap()
            .identity
    );
    let other = PointerLoadIdentity::new(
        intern_c_memory(CMemory::new().with_block(PointerBlock::from("global:other"), 8)),
        cell.clone(),
    );
    assert_ne!(origin, other);
    assert_ne!(origin.cmp(&other), std::cmp::Ordering::Equal);
    let hash = |identity: &PointerLoadIdentity| {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        identity.hash(&mut hasher);
        hasher.finish()
    };
    assert_ne!(hash(&origin), hash(&other));
    assert_ne!(
        origin,
        PointerLoadIdentity::new(snapshot.clone(), cell.offset_by_bytes(8))
    );
    let view = input
        .clone()
        .with_type(CType::UInt8Pointer)
        .with_pointer(cell.offset_by_bytes(4));
    assert!(std::ptr::eq(
        input.designation().unwrap(),
        view.designation().unwrap()
    ));
    assert_eq!(
        c_value_declaration_variable(&CValue::Pointer(input.clone())),
        None
    );

    let target = Pointer::symbolic(Variable(410_071));
    let mut raw = TermRewrite::for_pointer_exact(&cell, &target);
    let CValue::Pointer(result) = raw.value(&CValue::Pointer(input.clone())) else {
        panic!()
    };
    assert_eq!(raw.refusal(), None);
    assert_eq!(result.pointer(), &target);
    assert!(std::ptr::eq(
        input.designation().unwrap(),
        result.designation().unwrap()
    ));
    drop(raw);

    let replacement = value(
        target.clone(),
        object(target.clone(), "member", IntegerTerm::constant_i64(1)),
    );
    let replacements = BTreeMap::from([(variable, TypedCReplacement::Pointer(replacement))]);
    let empty_integer = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut typed =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let CValue::Pointer(result) = typed.value(&CValue::Pointer(input)) else {
        panic!()
    };
    assert_eq!(typed.refusal(), None);
    let Some(PointerDesignation::Loaded(mapped)) = result.designation() else {
        panic!()
    };
    assert_eq!(mapped.memory().arena_id(), snapshot.arena_id());
    assert_eq!(mapped.address(), &target);
    assert_eq!(mapped, &PointerLoadIdentity::new(snapshot, target));
}

#[test]
fn loaded_designation_snapshot_variables_follow_scalar_load_substitution_and_collection() {
    let _session = VerificationSession::enter();
    let variable = Variable(410_072);
    let slot = Pointer {
        block: PointerBlock::from("global:slot"),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block(slot.block.clone(), 8).store(
        slot.clone(),
        CValue::Int32(Bitvector32Term::Variable(variable)),
    );
    let snapshot = intern_c_memory(memory);
    let cell = Pointer {
        block: slot.block.clone(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(variable)),
            byte_width: 8,
        },
    };
    let input = CValue::Pointer(value(
        Pointer::null(),
        PointerDesignation::Loaded(PointerLoadIdentity::new(snapshot.clone(), cell.clone())),
    ));
    let scalar = Bitvector32Term::MemoryLoad(snapshot, Box::new(cell), LoadKind::Bits32);
    let mut actual = BTreeSet::new();
    let mut expected = BTreeSet::new();
    crate::kernel::prelude::collect_c_value_bitvector_variables(&input, &mut actual);
    crate::kernel::prelude::collect_bitvector_variables(&scalar, &mut expected);
    assert_eq!(actual, expected);
    assert!(actual.contains(&variable));
    let target = Bitvector32Term::Constant(2);
    let mapped =
        crate::kernel::prelude::substitute_bitvector_variable_in_c_value(&input, variable, &target);
    let mapped_scalar =
        crate::kernel::prelude::substitute_bitvector_variable(&scalar, variable, &target);
    let CValue::Pointer(mapped) = mapped else {
        panic!()
    };
    let Some(PointerDesignation::Loaded(mapped)) = mapped.designation() else {
        panic!()
    };
    let Bitvector32Term::MemoryLoad(expected_memory, expected_address, _) = mapped_scalar else {
        panic!()
    };
    assert_eq!(mapped.memory().arena_id(), expected_memory.arena_id());
    assert_eq!(mapped.address(), expected_address.as_ref());
    assert_eq!(mapped.memory().memory().known_value(&slot), Some(int32(2)));
    assert_eq!(
        mapped,
        &PointerLoadIdentity::new(expected_memory, *expected_address)
    );
}

#[test]
fn loaded_designation_alpha_keys_rename_cells_but_retain_defining_snapshots() {
    let _session = VerificationSession::enter();
    let snapshot = intern_c_memory(CMemory::new());
    let later = intern_c_memory(CMemory::new().with_block(PointerBlock::from("global:later"), 8));
    let quantified = |variable, memory: SharedCMemory| Proposition::ForAll {
        var: variable,
        sort: Sort::CPointer(CType::Int32Pointer),
        body: Box::new(Proposition::Predicate {
            name: "loaded_designation".into(),
            arguments: vec![Term::CValue(CValue::Pointer(value(
                Pointer::null(),
                PointerDesignation::Loaded(PointerLoadIdentity::new(
                    memory,
                    Pointer::symbolic(variable),
                )),
            )))],
        }),
    };
    let a = quantified(Variable(410_073), snapshot.clone());
    let b = quantified(Variable(410_074), snapshot);
    let c = quantified(Variable(410_074), later);
    assert!(crate::kernel::proof::fact_keys::propositions_are_alpha_equal(&a, &b));
    assert!(!crate::kernel::proof::fact_keys::propositions_are_alpha_equal(&a, &c));
}

#[test]
fn loaded_designation_origin_keys_do_not_compare_unrelated_snapshot_contents() {
    let _session = VerificationSession::enter();
    let cell = Pointer::symbolic(Variable(410_075));
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let base = Pointer {
            block: PointerBlock::from("global:origin_key_noise"),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut memory = CMemory::new().with_block(base.block.clone(), (size as u32 + 1) * 8);
        for index in 0..size {
            memory = memory.store(
                base.offset_by_bytes(index as u32 * 8),
                CValue::UInt64(Bitvector32Term::UInt64Constant(index)),
            );
        }
        let left = PointerLoadIdentity::new(intern_c_memory(memory.clone()), cell.clone());
        let right = PointerLoadIdentity::new(
            intern_c_memory(memory.store(base.offset_by_bytes(size as u32 * 8), int32(1))),
            cell.clone(),
        );
        let same = left.clone();
        let ((), work) = crate::persistent::measure_persistent_work(|| {
            assert_eq!(left, same);
            assert_ne!(left, right);
            assert_ne!(left.cmp(&right), std::cmp::Ordering::Equal);
            let mut left_hash = std::collections::hash_map::DefaultHasher::new();
            let mut same_hash = std::collections::hash_map::DefaultHasher::new();
            left.hash(&mut left_hash);
            same.hash(&mut same_hash);
            assert_eq!(left_hash.finish(), same_hash.finish());
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= 8),
        "origin keys visited snapshot maps: {samples:?}"
    );
}

#[test]
fn loaded_designation_content_hash_is_stable_without_equating_distinct_arenas() {
    let cell = Pointer {
        block: PointerBlock::from("global:stable_load_origin"),
        offset: PointerOffsetTerm::Constant(0),
    };
    let create = || {
        let _session = VerificationSession::enter();
        let memory = CMemory::new().with_block(cell.block.clone(), 8);
        PointerLoadIdentity::new(intern_c_memory(memory), cell.clone())
    };
    let first = create();
    let second = create();
    // These operations inspect only retained immutable handles. They never
    // decode an old session's interned raw-address name in the new registry.
    assert_ne!(first.memory().arena_id(), second.memory().arena_id());
    assert_ne!(first, second);
    let hash = |identity: &PointerLoadIdentity| {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        identity.hash(&mut hasher);
        hasher.finish()
    };
    assert_eq!(hash(&first), hash(&second));
    let first = value(Pointer::null(), PointerDesignation::Loaded(first));
    let second = value(Pointer::null(), PointerDesignation::Loaded(second));
    assert_ne!(first, second);
    let carrier_hash = |value: &CPointerValue| {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        value.hash(&mut hasher);
        hasher.finish()
    };
    assert_eq!(carrier_hash(&first), carrier_hash(&second));
}

#[test]
fn loaded_pointer_pair_substitution_rewrites_one_defining_load_and_preserves_displacement() {
    let _session = VerificationSession::enter();
    let binder = Variable(410_076);
    let base = Pointer {
        block: PointerBlock::from("global:paired_load_cells"),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block(base.block.clone(), 64);
    let cell = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(binder)),
            byte_width: 8,
        },
    };
    let read = |cell: &Pointer| {
        let load = Bitvector32Term::MemoryLoad(
            intern_c_memory_ref(&memory),
            Box::new(cell.clone()),
            LoadKind::Pointer,
        );
        let (variable, _) = crate::kernel::eval::load_variable_for_term(&load).unwrap();
        let Bitvector32Term::MemoryLoad(memory, cell, _) =
            crate::kernel::eval::registered_load_term_for_variable(&variable).unwrap()
        else {
            panic!()
        };
        let identity = PointerLoadIdentity::new(memory, *cell);
        (variable, identity)
    };
    let (variable, identity) = read(&cell);
    let replacement = Bitvector32Term::Constant(2);
    let target_cell = crate::kernel::prelude::substitute_bitvector_variable_in_pointer(
        &cell,
        binder,
        &replacement,
    );
    let (target_variable, target_identity) = read(&target_cell);
    assert_ne!(variable, target_variable);
    for pointer in [
        Pointer::symbolic(variable).offset_by_bytes(4),
        Pointer::loaded(base.block.clone(), Bitvector32Term::Variable(variable), 4)
            .offset_by_bytes(4),
        Pointer::loaded_value(identity.memory(), identity.address()).offset_by_bytes(4),
    ] {
        let input = CValue::Pointer(value(pointer, PointerDesignation::Loaded(identity.clone())));
        let mapped = crate::kernel::prelude::substitute_bitvector_variable_in_c_value(
            &input,
            binder,
            &replacement,
        );
        let CValue::Pointer(mapped) = mapped else {
            panic!()
        };
        assert_eq!(
            mapped.designation(),
            Some(&PointerDesignation::Loaded(target_identity.clone()))
        );
        let CValue::Pointer(original) = input else {
            panic!()
        };
        match &original.pointer().block {
            PointerBlock::Symbolic(_) => {
                assert_eq!(
                    mapped.pointer(),
                    &Pointer::symbolic(target_variable).offset_by_bytes(4)
                );
            }
            PointerBlock::LoadedPointer(_) => {
                assert_eq!(
                    mapped.pointer(),
                    &Pointer::loaded_value(target_identity.memory(), target_identity.address())
                        .offset_by_bytes(4)
                );
            }
            _ => {
                assert_eq!(
                    mapped.pointer(),
                    &Pointer::loaded(
                        base.block.clone(),
                        Bitvector32Term::Variable(target_variable),
                        4
                    )
                    .offset_by_bytes(4)
                );
            }
        }
    }
    // A full typed binder substitution also updates the paired raw load.
    let input = CValue::Pointer(value(
        Pointer::symbolic(variable),
        PointerDesignation::Loaded(identity),
    ));
    let replacements = BTreeMap::from([(binder, TypedCReplacement::Bitvector(replacement))]);
    let empty_integer = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut rewrite =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let CValue::Pointer(mapped) = rewrite.value(&input) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    assert_eq!(mapped.pointer(), &Pointer::symbolic(target_variable));
    assert_eq!(
        mapped.designation(),
        Some(&PointerDesignation::Loaded(target_identity))
    );
}

#[test]
fn designation_is_full_value_identity_and_shared_across_address_and_view_changes() {
    let p = Pointer::symbolic(Variable(410_001));
    let first = value(
        p.clone(),
        object(p.clone(), "first", IntegerTerm::constant_i64(1)),
    );
    let second = value(
        p.clone(),
        object(p.clone(), "second", IntegerTerm::constant_i64(1)),
    );
    assert_eq!(first.pointer(), second.pointer());
    assert_ne!(first, second);
    assert_ne!(first.cmp(&second), std::cmp::Ordering::Equal);
    let hash = |pointer: &CPointerValue| {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        pointer.hash(&mut hasher);
        hasher.finish()
    };
    assert_ne!(hash(&first), hash(&second));
    let changed = first
        .clone()
        .with_type(CType::UInt8Pointer)
        .with_pointer(Pointer {
            block: p.block,
            offset: PointerOffsetTerm::Constant(4),
        });
    assert!(std::ptr::eq(
        first.designation().unwrap(),
        changed.designation().unwrap()
    ));
    let constant = first.clone().with_pointee_constant(true);
    assert_eq!(first, constant);
    assert_eq!(hash(&first), hash(&constant));
    let legacy = CPointerValue::new(Pointer::null(), CType::Int32Pointer);
    let mut old_hash = std::collections::hash_map::DefaultHasher::new();
    (
        legacy.pointer(),
        &legacy.c_type(),
        legacy.pointee_volatile(),
    )
        .hash(&mut old_hash);
    assert_eq!(hash(&legacy), old_hash.finish());
}

#[test]
fn typed_pointer_substitution_transports_domain_without_rebasing_it() {
    let source = Variable(410_010);
    let target = Pointer::symbolic(Variable(410_011));
    let actual = value(
        target.clone(),
        object(target.clone(), "array", IntegerTerm::constant_i64(16)),
    )
    .with_pointee_volatile(true);
    let occurrence = value(
        Pointer {
            block: PointerBlock::Symbolic(source),
            offset: PointerOffsetTerm::Constant(12),
        },
        PointerDesignation::Unresolved(source),
    );
    let replacements = BTreeMap::from([(source, TypedCReplacement::Pointer(actual.clone()))]);
    let empty_integer = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut rewrite =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(occurrence.clone())) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    assert_eq!(result.offset, PointerOffsetTerm::Constant(12));
    assert_eq!(result.designation(), actual.designation());
    assert!(result.pointee_volatile());
    let unrelated = value(Pointer::null(), PointerDesignation::Unresolved(source));
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(unrelated)) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    assert_eq!(result.pointer(), &Pointer::null());
    assert_eq!(result.designation(), actual.designation());
    assert!(!result.pointee_volatile());
    let mut address_only = TermRewrite::for_pointer_variable(source, &target);
    let CValue::Pointer(result) = address_only.value(&CValue::Pointer(occurrence)) else {
        panic!()
    };
    assert_eq!(address_only.refusal(), None);
    assert_eq!(
        result.designation(),
        Some(&PointerDesignation::Unresolved(source))
    );
    let explicit = value(
        Pointer::symbolic(source),
        object(
            Pointer::symbolic(source),
            "member",
            IntegerTerm::constant_i64(1),
        ),
    );
    let mut exact = TermRewrite::for_pointer_exact(explicit.pointer(), &target);
    let CValue::Pointer(result) = exact.value(&CValue::Pointer(explicit.clone())) else {
        panic!()
    };
    assert_eq!(exact.refusal(), None);
    assert_eq!(result.pointer(), &target);
    assert!(std::ptr::eq(
        result.designation().unwrap(),
        explicit.designation().unwrap()
    ));
    drop(exact);
    let mut typed =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let CValue::Pointer(result) = typed.value(&CValue::Pointer(explicit)) else {
        panic!()
    };
    assert_eq!(typed.refusal(), None);
    let Some(PointerDesignation::Object { root, base, .. }) = result.designation() else {
        panic!()
    };
    assert_eq!(root, &target);
    assert_eq!(base, &target);
}

#[test]
fn designation_terms_participate_in_math_substitution_and_variable_collection() {
    let c = Variable(410_020);
    let math = Variable(410_021);
    let p = Pointer::symbolic(c);
    let input = value(
        Pointer::null(),
        PointerDesignation::Object {
            root: p.clone(),
            base: p,
            path: vec![PointerDomainSelection::Element(
                IntegerTerm::var(math).into(),
            )]
            .into(),
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::var(math).into(),
        },
    );
    let mut carriers = CarrierVariables::for_rewrite(false);
    collect_c_pointer_carriers(&input, &mut carriers);
    assert_eq!(carriers.c, BTreeSet::from([c]));
    assert_eq!(carriers.integer, BTreeSet::from([math]));
    let mut capture = BTreeSet::new();
    let proposition = Proposition::Equal(
        Term::CValue(CValue::Pointer(input.clone())),
        Term::CValue(CValue::Void),
    );
    crate::kernel::prelude::collect_proposition_capture_variables(&proposition, &mut capture);
    assert!(capture.contains(&c));
    let integer_replacements = BTreeMap::from([(math, IntegerTerm::constant_i64(7))]);
    let empty_c = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut rewrite =
        TermRewrite::for_typed_variables(&empty_c, &integer_replacements, &empty_algebraic);
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(input)) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    let Some(PointerDesignation::Object { path, count, .. }) = result.designation() else {
        panic!()
    };
    assert_eq!(count.as_ref(), &IntegerTerm::constant_i64(7));
    assert_eq!(
        path[0],
        PointerDomainSelection::Element(IntegerTerm::constant_i64(7).into())
    );
}

#[test]
fn unresolved_designation_uses_the_pointer_binder_in_alpha_keys_and_capture_avoidance() {
    let source = Variable(410_030);
    let captured = Variable(410_031);
    let occurrence = value(
        Pointer::symbolic(source),
        PointerDesignation::Unresolved(source),
    );
    let replacement = value(Pointer::null(), PointerDesignation::Unresolved(captured));
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
        name: "Node".into(),
        fields: vec![AlgebraicValueType::C(CType::Int32Pointer)],
    }]
    .into();
    let algebraic_type = AlgebraicType {
        rigid: false,
        name: "DesignationScope".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            AlgebraicValueType::Algebraic {
                name: "DesignationScope".into(),
                arguments: vec![],
            },
            variants,
        )]))),
    };
    let expression = Bitvector32Term::AlgebraicMatch {
        scrutinee: Box::new(AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(410_032)),
        }),
        arms: vec![AlgebraicBitvectorMatchArm {
            variant: "Node".into(),
            bindings: vec![AlgebraicValue::C(CValue::Pointer(value(
                Pointer::symbolic(captured),
                PointerDesignation::Unresolved(captured),
            )))],
            body: Bitvector32Term::ClickFunctionApplication {
                name: "observe_designation".into(),
                arguments: vec![
                    PureFunctionArgument::Value(CValue::Pointer(occurrence)),
                    PureFunctionArgument::Value(CValue::Pointer(value(
                        Pointer::symbolic(captured),
                        PointerDesignation::Unresolved(captured),
                    ))),
                ],
            },
        }],
    };
    let replacements = BTreeMap::from([(source, TypedCReplacement::Pointer(replacement))]);
    let empty_integer = BTreeMap::new();
    let empty_algebraic = BTreeMap::new();
    let mut rewrite =
        TermRewrite::for_typed_variables(&replacements, &empty_integer, &empty_algebraic);
    let Bitvector32Term::AlgebraicMatch { arms, .. } = rewrite.bits(&expression) else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    let AlgebraicValue::C(CValue::Pointer(binding)) = &arms[0].bindings[0] else {
        panic!()
    };
    let PointerBlock::Symbolic(renamed) = binding.block else {
        panic!()
    };
    assert_ne!(renamed, captured);
    assert_eq!(
        binding.designation(),
        Some(&PointerDesignation::Unresolved(renamed))
    );
    let Bitvector32Term::ClickFunctionApplication { arguments, .. } = &arms[0].body else {
        panic!()
    };
    let PureFunctionArgument::Value(CValue::Pointer(result)) = &arguments[0] else {
        panic!()
    };
    assert_eq!(
        result.designation(),
        Some(&PointerDesignation::Unresolved(captured))
    );
    let PureFunctionArgument::Value(CValue::Pointer(bound)) = &arguments[1] else {
        panic!()
    };
    assert_eq!(
        bound.designation(),
        Some(&PointerDesignation::Unresolved(renamed))
    );
    let domain_fact = |var| Proposition::Predicate {
        name: "designated_pointer".into(),
        arguments: vec![Term::CValue(CValue::Pointer(value(
            Pointer::null(),
            PointerDesignation::Unresolved(var),
        )))],
    };
    let quantified = |var| Proposition::ForAll {
        var,
        sort: Sort::CPointer(CType::Int32Pointer),
        body: Box::new(domain_fact(var)),
    };
    assert!(
        crate::kernel::proof::fact_keys::propositions_are_alpha_equal(
            &quantified(source),
            &quantified(captured)
        )
    );
    assert!(
        !crate::kernel::proof::fact_keys::propositions_are_alpha_equal(
            &quantified(source),
            &Proposition::ForAll {
                var: captured,
                sort: Sort::CPointer(CType::Int32Pointer),
                body: Box::new(domain_fact(source))
            },
        )
    );
}

#[test]
fn designation_math_dag_traversal_scales_linearly() {
    let mut measurements = Vec::new();
    for depth in [16, 32, 64] {
        let mut count = SharedIntegerTerm::from(IntegerTerm::var(Variable(410_040)));
        for _ in 0..depth {
            count = IntegerTerm::Add(count.clone(), count).into();
        }
        let input = value(
            Pointer::null(),
            object(Pointer::null(), "array", count.as_ref().clone()),
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut carriers = CarrierVariables::for_rewrite(false);
            collect_c_pointer_carriers(&input, &mut carriers);
            assert_eq!(carriers.integer, BTreeSet::from([Variable(410_040)]));
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 16, "{measurements:?}");
    }
}

#[test]
fn designation_binders_are_canonical_and_algebraic_scalar_traversal_sees_shared_math() {
    let binder = Variable(410_050);
    assert_eq!(
        c_value_declaration_variable(&CValue::Pointer(value(
            Pointer::symbolic(binder),
            PointerDesignation::Unresolved(binder),
        ))),
        Some(binder)
    );
    assert_eq!(
        c_value_declaration_variable(&CValue::Pointer(value(
            Pointer::symbolic(binder),
            PointerDesignation::Unresolved(Variable(410_051)),
        ))),
        None
    );
    assert_eq!(
        c_value_declaration_variable(&CValue::Pointer(value(
            Pointer::symbolic(binder),
            object(
                Pointer::symbolic(binder),
                "field",
                IntegerTerm::constant_i64(1)
            ),
        ))),
        None
    );
    let scalar = Bitvector32Term::Variable(Variable(410_052));
    let mut measurements = Vec::new();
    for depth in [16, 32, 64] {
        let mut count = SharedIntegerTerm::from(IntegerTerm::Machine(
            SharedMachineIntegerTerm::intern(MachineIntegerType::Int32, scalar.clone()),
        ));
        for _ in 0..depth {
            count = IntegerTerm::Add(count.clone(), count).into();
        }
        let term = AlgebraicTerm {
            algebraic_type: AlgebraicType {
                rigid: false,
                name: "DesignationPayload".into(),
                arguments: vec![],
                variants: vec![].into(),
                schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::new())),
            },
            node: AlgebraicTermNode::Constructor {
                variant: "Pointer".into(),
                fields: vec![AlgebraicValue::C(CValue::Pointer(value(
                    Pointer::null(),
                    object(Pointer::null(), "array", count.as_ref().clone()),
                )))],
            },
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut visited = Vec::new();
            term.for_each_bitvector_term(|term| visited.push(term.clone()));
            assert_eq!(visited, vec![scalar.clone()]);
        });
        measurements.push(work);
    }
    for pair in measurements.windows(2) {
        assert!(pair[1] <= 3 * pair[0] + 16, "{measurements:?}");
    }
}

#[test]
fn designation_raw_rewrite_modes_partition_shared_memos_under_caller_managed_binders() {
    let binder = Variable(410_060);
    let source = Pointer {
        block: PointerBlock::Symbolic(Variable(410_061)),
        offset: PointerOffsetTerm::Constant(7),
    };
    let target = Pointer::symbolic(Variable(410_062));
    let offset_target = PointerOffsetTerm::Constant(9);
    let call = |name: &str, arguments| Pointer {
        block: PointerBlock::PureFunctionApplication(SharedPureApplication::intern(
            name.into(),
            arguments,
        )),
        offset: PointerOffsetTerm::Constant(0),
    };
    let inner = call(
        "domain_cache_inner",
        vec![PureFunctionArgument::Value(CValue::typed_pointer(
            source.clone(),
            CType::Int32Pointer,
        ))],
    );
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let load =
        crate::kernel::eval::load_variable_for_exact_cell(&memory, &source, LoadKind::Bits32, 4);
    let count: SharedIntegerTerm = IntegerTerm::Add(
        IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
            "domain_cache_extent".into(),
            vec![PureFunctionArgument::Value(CValue::typed_pointer(
                inner.clone(),
                CType::Int32Pointer,
            ))],
        ))
        .into(),
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load),
        ))
        .into(),
    )
    .into();
    let address = call(
        "domain_cache_outer",
        vec![
            PureFunctionArgument::Value(CValue::typed_pointer(inner, CType::Int32Pointer)),
            PureFunctionArgument::Integer(count.clone()),
        ],
    );
    let designation = PointerDesignation::Object {
        root: address.clone(),
        base: address.clone(),
        path: vec![PointerDomainSelection::Element(count.clone())].into(),
        element_type: CType::Int32,
        stride: 4,
        count: count.clone(),
    };
    let input = value(address.clone(), designation.clone());
    for mode in 0..3 {
        for domain_first in [false, true] {
            let mut rewrite = match mode {
                0 => TermRewrite::for_pointer_variable(Variable(410_061), &target),
                1 => TermRewrite::for_pointer_exact(&source, &target),
                _ => TermRewrite::for_pointer_offset_exact(&source.offset, &offset_target),
            };
            rewrite.enable_registered_load_resolution();
            // Pure-proposition callers manage ForAll/Exists scopes themselves;
            // TermRewrite::proposition deliberately keeps such scopes opaque.
            let scope = rewrite.push_c_substitution_scope(binder, binder);
            if domain_first {
                assert_eq!(rewrite.designation(&designation), designation);
            }
            let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(input.clone())) else {
                panic!()
            };
            assert_eq!(rewrite.refusal(), None);
            assert_ne!(
                result.pointer(),
                &address,
                "mode={mode} domain_first={domain_first}"
            );
            assert_eq!(
                result.designation(),
                Some(&designation),
                "mode={mode} domain_first={domain_first}"
            );
            assert_eq!(rewrite.designation(&designation), designation);
            assert_eq!(rewrite.refusal(), None);
            rewrite.pop_c_substitution_scope(scope);
        }
    }
    // Integer binders also rename terms in the retained descriptor even when
    // the only active source substitution changes raw pointer addresses.
    let integer = Variable(410_063);
    let renamed = Variable(410_064);
    let domain = PointerDesignation::Object {
        root: source.clone(),
        base: source.clone(),
        path: vec![PointerDomainSelection::Element(
            IntegerTerm::var(integer).into(),
        )]
        .into(),
        element_type: CType::Int32,
        stride: 4,
        count: IntegerTerm::var(integer).into(),
    };
    let mut rewrite = TermRewrite::for_pointer_variable(Variable(410_061), &target);
    let scope = rewrite.push_integer_substitution_scope(integer, renamed, false);
    let CValue::Pointer(result) = rewrite.value(&CValue::Pointer(value(source.clone(), domain)))
    else {
        panic!()
    };
    assert_eq!(rewrite.refusal(), None);
    let Some(PointerDesignation::Object {
        root,
        base,
        path,
        count,
        ..
    }) = result.designation()
    else {
        panic!()
    };
    assert_eq!(root, &source);
    assert_eq!(base, &source);
    assert_eq!(count.as_ref(), &IntegerTerm::var(renamed));
    assert_eq!(
        path[0],
        PointerDomainSelection::Element(IntegerTerm::var(renamed).into())
    );
    rewrite.pop_integer_substitution_scope(scope);
}

#[test]
fn numeric_rewriting_cannot_replace_pointer_integer_origin() {
    let _session = VerificationSession::enter();
    let original = value(
        Pointer::symbolic(Variable(410_080)),
        PointerDesignation::Unresolved(Variable(410_080)),
    );
    let other = value(
        Pointer::symbolic(Variable(410_081)),
        PointerDesignation::Unresolved(Variable(410_081)),
    );
    let encoded = CPointerIntegerValue::from_pointer(original.clone(), CType::UInt64).unwrap();
    let from = encoded.bits().clone();
    let to = Bitvector32Term::pointer_address(other.pointer().clone());
    let mut rewrite = TermRewrite::for_bits(&from, &to);
    let CValue::PointerInteger(rewritten) =
        rewrite.value(&CValue::PointerInteger(std::sync::Arc::new(encoded)))
    else {
        panic!("rewriting preserves pointer-integer sort");
    };
    assert_eq!(rewrite.refusal(), None);
    assert_eq!(rewritten.bits(), &to);
    assert_eq!(rewritten.origin(), &original);
    assert_ne!(rewritten.origin(), &other);
    drop(rewrite);

    // Plain integers never gain the origin of numerically equal pointer bits.
    let mut rewrite = TermRewrite::for_bits(&from, &to);
    assert_eq!(
        rewrite.value(&CValue::UInt64(from.clone())),
        CValue::UInt64(to.clone())
    );
}

#[test]
fn pointer_integer_rewrite_reserves_designation_only_variables() {
    let _session = VerificationSession::enter();
    let root = Pointer::symbolic(Variable(410_090));
    let extent = Variable(410_091);
    let origin = value(
        root.clone(),
        object(root, "member", IntegerTerm::var(extent)),
    );
    let encoded = CPointerIntegerValue::from_pointer(origin, CType::UInt64).unwrap();
    // Even when numeric operations eliminate the address, its retained
    // descriptor remains a source of freshness dependencies.
    let encoded = encoded.with_parts(Bitvector32Term::UInt64Constant(0), encoded.origin().clone());
    let mut variables = CarrierVariables::default();
    collect_c_value_carriers(
        &CValue::PointerInteger(std::sync::Arc::new(encoded)),
        &mut variables,
    );
    assert!(variables.integer.contains(&extent));
    assert!(variables.c.contains(&Variable(410_090)));
}
