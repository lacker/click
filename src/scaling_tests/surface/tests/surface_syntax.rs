// Scaling tests of `src/surface/tests/surface_syntax.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn integer_symbolic_aliases_keep_simple_verification_bounded() {
    let mut measured = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut source = String::from("theorem aliases(x: Integer) { let a0: Integer = x;\n");
        for index in 1..=depth {
            source.push_str(&format!(
                "let a{index}: Integer = a{} + a{};\n",
                index - 1,
                index - 1
            ));
        }
        source.push_str(&format!(
            "requires a{depth} == a{depth};\n\
             ensures a{depth} == a{depth} by {{ close(); }} }}"
        ));
        let (result, work) =
            crate::instrumentation::measure_deterministic_work(|| verify_click_theorems(&source));
        result.unwrap_or_else(|error| panic!("depth {depth}: {}", error.message()));
        measured.push(work);
    }
    for pair in measured.windows(2) {
        assert!(
            pair[1] <= 3 * pair[0],
            "alias traversal must not expand the tree: {measured:?}"
        );
    }
}

#[test]
fn indexed_surface_resolution_ignores_unrelated_available_facts() {
    let surface = ClickProposition::Comparison {
        left: current_var("x"),
        operator: ComparisonOperator::Equal,
        right: current_int(1),
    };
    let target = Proposition::condition_is(ConditionTerm::Constant(true), true);
    let mut spellings = SurfacePropositionMap::default();
    spellings.record_lowering(&surface, &target).unwrap();
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut available = std::collections::BTreeSet::from([target.clone()]);
            available.extend((0..size).map(|index| {
                Proposition::condition_is(ConditionTerm::Variable(Variable(95_000 + index)), true)
            }));
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                spellings.available_kernel_matching(&surface, |kernel| available.contains(kernel))
            });
            assert_eq!(resolved, Some(&target));
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed indexed surface lookup should ignore unrelated facts: {samples:?}"
    );
}

/// A nested implication records every suffix of its chain, which a map that
/// copied or rendered each recorded sub-proposition paid for as the sum of
/// all suffix sizes: 0.17, 0.35, 0.80 and 3.36 seconds of debug `click
/// verify` at depths 64 to 512 (`supported_implication_boundary_*` in
/// `src/bin/click.rs` is the realistic case). Interning each node once makes
/// recording linear in the chain, a repeat of a recorded chain a lookup, and
/// every suffix still answers for its own surface.
#[test]
fn nested_implication_lowering_records_in_linear_work() {
    fn chain(depth: u32) -> (ClickProposition, Proposition) {
        let atom = |index: u32| {
            (
                ClickProposition::Comparison {
                    left: current_var(&format!("x{}", index % 2)),
                    operator: ComparisonOperator::Equal,
                    right: current_int(index % 3),
                },
                Proposition::condition_is(
                    ConditionTerm::Variable(Variable(u64::from(300_000 + index % 6))),
                    true,
                ),
            )
        };
        let (mut surface, mut kernel) = atom(depth);
        for index in (0..depth).rev() {
            let (left_surface, left_kernel) = atom(index);
            surface = ClickProposition::Implies(Box::new(left_surface), Box::new(surface));
            kernel = Proposition::Implies(Box::new(left_kernel), Box::new(kernel));
        }
        (surface, kernel)
    }
    fn suffix(mut proposition: &Proposition, depth: u32) -> &Proposition {
        for _ in 0..depth {
            let Proposition::Implies(_, right) = proposition else {
                unreachable!("a chain suffix is an implication or its last atom")
            };
            proposition = right;
        }
        proposition
    }
    fn surface_suffix(mut proposition: &ClickProposition, depth: u32) -> &ClickProposition {
        for _ in 0..depth {
            let ClickProposition::Implies(_, right) = proposition else {
                unreachable!("a chain suffix is an implication or its last atom")
            };
            proposition = right;
        }
        proposition
    }
    let copied = || crate::surface::CLICK_PROPOSITION_NODES_COPIED.with(std::cell::Cell::get);
    let mut samples = Vec::new();
    for depth in [64u32, 128, 256, 512] {
        let (surface, kernel) = chain(depth);
        let mut spellings = SurfacePropositionMap::default();
        let copies_before = copied();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            spellings.record_lowering(&surface, &kernel).unwrap();
        });
        let copies = copied() - copies_before;
        let copies_before = copied();
        let ((), repeat_work) = crate::instrumentation::measure_deterministic_work(|| {
            spellings.record_lowering(&surface, &kernel).unwrap();
        });
        let repeat_copies = copied() - copies_before;
        for position in [0, 1, depth / 2, depth - 1, depth] {
            assert_eq!(
                spellings.surface(suffix(&kernel, position)).unwrap(),
                surface_suffix(&surface, position),
                "depth {depth}: suffix {position} keeps its own surface"
            );
        }
        assert_eq!(repeat_copies, 0, "depth {depth}: a repeat copies nothing");
        samples.push((depth, work, copies, repeat_work));
    }
    for pair in samples.windows(2) {
        let ((_, work, copies, repeat), (_, next_work, next_copies, next_repeat)) =
            (pair[0], pair[1]);
        assert!(
            next_work <= 2 * work + 16 && next_copies <= 2 * copies + 16,
            "recording should be linear in the chain: {samples:?}"
        );
        assert!(
            next_repeat <= 2 * repeat + 16,
            "a repeat should be linear in the chain: {samples:?}"
        );
    }
    let (depth, work, copies, _) = samples[samples.len() - 1];
    let nodes = 2 * depth as usize + 1;
    assert!(
        work >= nodes && work <= 8 * nodes && copies <= 2 * nodes,
        "recording charges its nodes and copies the chain once: {samples:?}"
    );
}

#[test]
fn qualified_storage_source_index_preserves_forks_and_scales() {
    fn pair(index: u32) -> (Address, ContractExpression, ClickProposition, Proposition) {
        let pointer = Address {
            base: AddressBase::Concrete(format!("global:state#file-static:file{index}.c")),
            offset: AddressOffset::Constant(0),
        };
        let expression = ContractExpression::QualifiedC {
            name: format!("file{index}::state"),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(ProgramExpression::Value(ProgramValue::Pointer(
                    crate::kernel::Pointer::new(pointer.clone(), ProgramType::UInt64Pointer),
                ))),
                value_type: ProgramType::UInt64,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            },
        };
        let surface = ClickProposition::Comparison {
            left: expression.clone(),
            operator: ComparisonOperator::Equal,
            right: current_int(index),
        };
        let kernel = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::read_named(
                    crate::kernel::ProgramPoint::at(
                        &(crate::kernel::intern_memory(SymbolicMemory::new())),
                    ),
                    Box::new(pointer.clone()),
                    crate::kernel::LoadKind::Int32,
                )),
                right: Box::new(MachineTerm::uint64_constant(u64::from(index))),
            },
            true,
        );
        (pointer, expression, surface, kernel)
    }
    for size in [16_u32, 64, 256, 1024] {
        let mut sources = SurfacePropositionMap::default();
        for i in 0..size {
            let (_, _, surface, kernel) = pair(i);
            sources.record_lowering(&surface, &kernel).unwrap();
        }
        let ancestor = sources.clone();
        assert!(sources.shares_persistent_storage_with(&ancestor));
        let (pointer, expression, surface, kernel) = pair(size);
        let before = crate::persistent::persistent_node_allocations();
        sources.record_lowering(&surface, &kernel).unwrap();
        let allocations = crate::persistent::persistent_node_allocations() - before;
        assert!(
            allocations <= 16 * (size.ilog2() as usize + 1) + 32,
            "{size}: {allocations}"
        );
        assert!(
            ancestor
                .storage
                .qualified_load_sources
                .get(&pointer)
                .is_none()
        );
        assert_eq!(
            sources.storage.qualified_load_sources.get(&pointer),
            Some(&expression)
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            sources.storage.qualified_load_sources.get(&pointer)
        });
        assert!(
            work <= 4 * (size.ilog2() as usize + 1) + 4,
            "{size}: {work}"
        );
    }
}

#[test]
fn requirement_spelling_selects_one_recorded_enclosing_clause() {
    let target = Proposition::condition_is(ConditionTerm::Variable(Variable(8000)), true);
    let mut work = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut spellings = SurfacePropositionMap::default();
        let mut latest = None;
        for index in 0..size {
            let surface = ClickProposition::Comparison {
                left: current_var(&format!("source{index}")),
                operator: ComparisonOperator::Equal,
                right: current_int(1),
            };
            let guarded = Proposition::And(
                Box::new(target.clone()),
                Box::new(Proposition::condition_is(
                    ConditionTerm::Variable(Variable(index)),
                    true,
                )),
            );
            spellings.record_lowering(&surface, &guarded).unwrap();
            latest = Some(surface);
        }
        assert!(spellings.recorded_surface(&target).is_none());
        let (selected, cost) = crate::instrumentation::measure_deterministic_work(|| {
            spellings.recorded_requirement_surface(&target)
        });
        assert_eq!(selected, latest.as_ref());
        assert!(
            spellings
                .recorded_requirement_surface(&Proposition::Not(Box::new(target.clone())))
                .is_none()
        );
        work.push(cost);
    }
    assert!(work.iter().all(|cost| *cost == work[0]), "{work:?}");
}
