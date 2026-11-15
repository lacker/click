// Scaling tests of `src/surface/proof/selected_arithmetic.rs`: deterministic
// work and proof construction measured at several input sizes.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::surface::proof::pure_theorems::PureTheoremContext;

#[test]
fn failed_integer_bridge_does_not_construct_unused_facts() {
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let value = MachineTerm::Variable(Variable(910_001));
        let written =
            ContractExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
        let mut facts = Vec::new();
        let mut surfaces = SurfacePropositionMap::default();
        for index in 0..size {
            let fact = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(value.clone()),
                    right: Box::new((100 + index).into()),
                },
                true,
            );
            let surface = relate(
                written.clone(),
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(100 + index))),
                Relation::Less,
            );
            surfaces.record_lowering(&surface, &fact).unwrap();
            facts.push(fact);
        }
        let context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            memory: Memory::new(),
            values: BTreeMap::from([("x".into(), ProgramValue::Int32(value))]),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements: surfaces,
        };
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let theorems = TheoremEnvironment::with_standard_library(&[]).unwrap();
        let definitions = SpecDefinitions::new(&predicates, &functions);
        // `to_integer(x) + 1` is Integer arithmetic, so the goals stay Integer
        // claims: `to_integer(x) <= -1` alone would be the native `x <= -1`,
        // which plain selected-premise arithmetic decides with no bridge.
        let successor = ContractExpression::Add(
            Box::new(to_integer(&written)),
            Box::new(integer_literal("1")),
        );
        let surface_goal = relate(successor.clone(), integer_literal("0"), Relation::LessEqual);
        let lowering = Proof::for_pure_goal(
            "unprovable bridge",
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            &context,
            definitions,
            &theorems,
        );
        let goal = lowering
            .lower_surface_proposition(&surface_goal, "test goal")
            .unwrap();
        let proof = Proof::for_pure_surface_goal(
            "unprovable bridge",
            &facts,
            goal,
            surface_goal,
            &context,
            definitions,
            &theorems,
        );
        let before = BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::try_bridged_selected_arithmetic(&(proof))
        });
        assert!(
            result.unwrap().is_none(),
            "upper bounds do not imply x + 1 <= 0"
        );
        let constructions = BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get) - before;
        assert_eq!(
            constructions, 0,
            "an unprovable goal must not construct bridge facts"
        );
        let positive_surface = relate(successor, integer_literal("100"), Relation::LessEqual);
        let positive_goal = lowering
            .lower_surface_proposition(&positive_surface, "positive bridge goal")
            .unwrap();
        let positive = Proof::for_pure_surface_goal(
            "one selected bridge",
            &facts,
            positive_goal,
            positive_surface,
            &context,
            definitions,
            &theorems,
        );
        let before = BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get);
        let closed =
            crate::kernel::search::ProofSearch::try_bridged_selected_arithmetic(&(positive))
                .unwrap()
                .expect("the bound x < 100 proves x + 1 <= 100");
        assert!(closed.is_complete());
        // Selected-premise arithmetic reads the native bound `x < 100` as its Integer reading,
        // the same fact in its one form, so no carrying bridge is built.
        assert_eq!(
            BRIDGE_ESTABLISHMENTS.with(std::cell::Cell::get) - before,
            0,
            "a native bound needs no constructed bridge"
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
        "{samples:?}"
    );
    eprintln!("unprovable integer bridge work: {samples:?}");
}

#[test]
fn disequality_refutation_work_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let (k, j, y) = (
            MachineTerm::Variable(Variable(911_001)),
            MachineTerm::Variable(Variable(911_002)),
            MachineTerm::Variable(Variable(911_003)),
        );
        let written = |name: &str| {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(name.into()))
        };
        let mut surfaces = SurfacePropositionMap::default();
        let order = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(k.clone()),
                right: Box::new(j.clone()),
            },
            true,
        );
        surfaces
            .record_lowering(&relate(written("k"), written("j"), Relation::Less), &order)
            .unwrap();
        let mut facts = vec![order];
        // Bounds on an unrelated value, which the refutation of `k == j`
        // never reads.
        for index in 0..size {
            let fact = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(y.clone()),
                    right: Box::new((100 + index).into()),
                },
                true,
            );
            let surface = relate(
                written("y"),
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(100 + index))),
                Relation::Less,
            );
            surfaces.record_lowering(&surface, &fact).unwrap();
            facts.push(fact);
        }
        let context = PureTheoremContext {
            diagnostic_names: Default::default(),
            declaration_bindings: BTreeMap::new(),
            integer_values: crate::persistent::PersistentMap::default(),
            memory: Memory::new(),
            values: BTreeMap::from([
                ("k".into(), ProgramValue::Int32(k)),
                ("j".into(), ProgramValue::Int32(j)),
                ("y".into(), ProgramValue::Int32(y)),
            ]),
            array_refs: BTreeMap::new(),
            requires: facts.clone(),
            surface_requirements: surfaces,
        };
        let predicates = PredicateEnvironment::new(&[]);
        let functions = ClickFunctionEnvironment::new(&[]);
        let theorems = TheoremEnvironment::with_standard_library(&[]).unwrap();
        let definitions = SpecDefinitions::new(&predicates, &functions);
        let surface_goal = ClickProposition::Comparison {
            left: written("k"),
            operator: ComparisonOperator::NotEqual,
            right: written("j"),
        };
        let lowering = Proof::for_pure_goal(
            "disequality",
            &facts,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            &context,
            definitions,
            &theorems,
        );
        let goal = lowering
            .lower_surface_proposition(&surface_goal, "test goal")
            .unwrap();
        let proof = Proof::for_pure_surface_goal(
            "disequality",
            &facts,
            goal,
            surface_goal,
            &context,
            definitions,
            &theorems,
        );
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::try_disequality_by_selected_refutation(&(proof))
        });
        let closed = result.unwrap().expect("k < j refutes k == j, so k != j");
        assert!(closed.is_complete());
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0]),
        "{samples:?}"
    );
    eprintln!("disequality refutation work: {samples:?}");
}

#[test]
fn retained_machine_rewrite_admission_reads_only_comparison_roots() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelTermExport, KernelTermImport, MachineBinaryOp,
        SharedMachineIntegerTerm,
    };
    for format in [
        MachineIntegerType::Int32,
        MachineIntegerType::UInt64,
        MachineIntegerType::Int128,
    ] {
        let mut previous = None;
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut root = KernelTermImport::default()
                .machine(format, &MachineTerm::Variable(Variable(995454)));
            let leaf = root.clone();
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root, leaf.clone()],
                );
            }
            let side = |root| {
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(format, root).unwrap())
                    .into()
            };
            let proposition =
                Proposition::ConditionIs(ConditionTerm::IntegerEqual(side(root), side(leaf)), true);
            let exports = KernelTermExport::machine_export_count();
            let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
                is_rewrite_equality(&proposition)
            });
            assert_eq!(accepted, format.format().bits() <= 64);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            if let Some(before) = previous {
                assert_eq!(work, before);
            }
            previous = Some(work);
        }
    }
}

#[test]
fn rewrite_history_keys_share_call_carriers_and_keep_state_authority() {
    use super::search::RewriteGoalKey;
    use crate::kernel::{
        KernelTermImport, PointerValue, PureFunctionArgument, SharedMachineIntegerTerm,
        SharedPureApplication,
    };
    let mut samples = Vec::new();
    for depth in [4, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(995941));
        let before = Memory::new();
        let after = before
            .clone()
            .store(pointer.clone(), ProgramValue::Int32(7u32.into()));
        let goal = |memory, format| {
            let application = SharedPureApplication::intern(
                "read_length".into(),
                vec![PureFunctionArgument::ArrayRef {
                    memory,
                    pointer: ProgramValue::Pointer(PointerValue::new(
                        pointer.clone(),
                        ProgramType::Int32Pointer,
                    )),
                    element_type: ProgramType::Int32,
                }],
            );
            let mut root = KernelTermImport::default().machine_call(format, &application);
            for _ in 0..depth {
                let application = SharedPureApplication::intern(
                    "nested_length".into(),
                    vec![PureFunctionArgument::SharedMachine(
                        SharedMachineIntegerTerm::from_shared(format, root).unwrap(),
                    )],
                );
                root = KernelTermImport::default().machine_call(format, &application);
            }
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format,
                    relation: CompareRelation::Equal,
                    left: Box::new(root.machine_conversion_leaf().unwrap().clone()),
                    right: Box::new(
                        crate::kernel::machine_integer::range::constant_word(format, &0.into())
                            .unwrap(),
                    ),
                },
                true,
            )
        };
        let a = goal(before.clone(), MachineIntegerType::UInt64);
        let b = goal(before.clone(), MachineIntegerType::UInt64);
        assert_ne!(a, b, "fresh exact producer handles");
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        let ((ka, kb), work) = crate::instrumentation::measure_deterministic_work(|| {
            (RewriteGoalKey::new(&a), RewriteGoalKey::new(&b))
        });
        assert!(matches!(ka, RewriteGoalKey::Identity(_)));
        assert_eq!(ka, kb, "one rewrite goal despite fresh carriers");
        assert_ne!(
            ka,
            RewriteGoalKey::new(&goal(after, MachineIntegerType::UInt64))
        );
        assert_ne!(
            ka,
            RewriteGoalKey::new(&goal(before, MachineIntegerType::Int64))
        );
        let mut negated = b;
        let Proposition::ConditionIs(_, wanted) = &mut negated else {
            unreachable!()
        };
        *wanted = false;
        assert_ne!(ka, RewriteGoalKey::new(&negated));
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples[1] <= 5 * samples[0] && samples[2] <= 5 * samples[1],
        "{samples:?}"
    );
}
