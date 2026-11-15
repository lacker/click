// Scaling tests of `src/kernel/tests/canonicalization_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Collecting the variables of a load counts each state the load reaches
/// once, not once per path to it. Each level of the DAG is reached through
/// two cells of the level above, so walking it as a tree visited `2^depth`
/// states, uncharged; depth 32 did not finish.
#[test]
fn variable_collection_walks_a_shared_state_dag_once() {
    let samples = [8usize, 16, 32, 64].map(|depth| {
        let load = nested_state_load(depth);
        crate::kernel::reasoning::variable_collection::clear_shared_memory_variables();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            crate::kernel::reasoning::collect_bitvector_variables(&load, &mut variables);
        });
        (depth, work)
    });
    for (depth, work) in samples {
        assert!(work >= depth, "counting a state is charged: {samples:?}");
    }
    for pair in samples.windows(2) {
        let ((_, work), (_, next_work)) = (pair[0], pair[1]);
        assert!(
            next_work <= 2 * work + 8,
            "collection should be linear in the DAG depth: {samples:?}"
        );
    }
}

/// A state one store past a counted one is counted from that one's
/// variables by the entries the store changed, not by walking every cell:
/// collecting the variables of a load after the store costs the same beside
/// 16 to 1024 unrelated cells. Counting each reached state whole made the
/// collection linear in the unrelated cells, which is what made a round
/// trip's extra copy grow with the unrelated allocations beside it.
#[test]
fn variable_collection_after_a_store_costs_the_store() {
    let block = PointerBlock::Concrete("counted-history".to_string());
    let at = |offset: i64| Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let samples = [16usize, 64, 256, 1024].map(|cells| {
        let mut memory = Memory::new().with_block("counted-history", 4 * cells as u32 + 8);
        for index in 0..cells {
            memory = memory.store(
                at(4 * index as i64),
                ProgramValue::Int32(MachineTerm::Variable(Variable(7_000_000 + index as u64))),
            );
        }
        let before = crate::kernel::intern_memory(memory.clone());
        crate::kernel::reasoning::variable_collection::clear_shared_memory_variables();
        let mut variables = BTreeSet::new();
        crate::kernel::reasoning::collect_bitvector_variables(
            &MachineTerm::MemoryLoad(before, Box::new(at(0)), crate::kernel::LoadKind::Int32),
            &mut variables,
        );
        assert_eq!(variables.len(), cells);
        let after = memory.store(
            at(0),
            ProgramValue::Int32(MachineTerm::Variable(Variable(7_900_000))),
        );
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(after),
            Box::new(at(4)),
            crate::kernel::LoadKind::Int32,
        );
        let (variables, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut variables = BTreeSet::new();
            crate::kernel::reasoning::collect_bitvector_variables(&load, &mut variables);
            variables
        });
        assert!(variables.contains(&Variable(7_900_000)));
        assert!(
            !variables.contains(&Variable(7_000_000)),
            "the overwritten cell's variable leaves"
        );
        assert_eq!(variables.len(), cells);
        (cells, work)
    });
    let (_, first) = samples[0];
    assert!(
        samples.iter().all(|(_, work)| *work <= first + 4),
        "a store's collection grows with unrelated cells: {samples:?}"
    );
}
