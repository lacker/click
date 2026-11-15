use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

/// [`allocation_continuity`] of two 32-bit extents.
fn int32_continuity(
    input_base: &Pointer,
    input_bytes: &MachineTerm,
    output_base: &Pointer,
    output_bytes: &MachineTerm,
    assumptions: &PureFactContext,
) -> AllocationContinuity {
    allocation_continuity(
        input_base,
        &HeapExtent::int32(input_bytes.clone()),
        output_base,
        &HeapExtent::int32(output_bytes.clone()),
        assumptions,
    )
}

/// Two extents of different formats are never one allocation's (D5): a pair
/// at one base, or at bases not proven distinct (two external pointers), is
/// refused rather than compared, and distinct blocks stay distinct. Two 64-bit extents compare
/// at 64 bits.
#[test]
fn continuity_refuses_extents_of_different_formats() {
    let base = Pointer {
        block: PointerBlock::Heap(930_200),
        offset: PointerOffsetTerm::Constant(0),
    };
    let other = Pointer {
        block: PointerBlock::Heap(930_201),
        offset: PointerOffsetTerm::Constant(0),
    };
    let count = MachineTerm::Variable(Variable(930_202));
    let wide = HeapExtent::new(
        MachineTerm::uint64_multiply(count.clone(), MachineTerm::uint64_constant(4)),
        HeapExtentKind::UInt64,
    );
    let narrow = HeapExtent::int32(MachineTerm::constant(16));
    let assumptions = PureFactContext::new();
    for (input, output) in [(&wide, &narrow), (&narrow, &wide)] {
        assert_eq!(
            allocation_continuity(&base, input, &base, output, &assumptions),
            AllocationContinuity::CrossKind,
        );
        assert_eq!(
            allocation_continuity(
                &external_pointer(930_203),
                input,
                &external_pointer(930_205),
                output,
                &assumptions,
            ),
            AllocationContinuity::CrossKind,
        );
        assert_eq!(
            allocation_continuity(&base, input, &other, output, &assumptions),
            AllocationContinuity::Distinct,
        );
    }
    assert_eq!(
        allocation_continuity(&base, &wide, &base, &wide, &assumptions),
        AllocationContinuity::Same,
    );
    let other_wide = HeapExtent::new(
        MachineTerm::uint64_multiply(
            MachineTerm::Variable(Variable(930_204)),
            MachineTerm::uint64_constant(4),
        ),
        HeapExtentKind::UInt64,
    );
    assert!(matches!(
        allocation_continuity(&base, &wide, &base, &other_wide, &assumptions),
        AllocationContinuity::Undecided(ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::Equal,
            ..
        }),
    ));
}

#[test]
fn contract_retirement_invalidates_creation_provenance_even_with_replacement() {
    let base = Pointer {
        block: PointerBlock::Heap(930_100),
        offset: PointerOffsetTerm::Constant(0),
    };
    let bytes = MachineTerm::constant(16);
    let input = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_allocation(base.clone(), bytes.clone()));
    let memory = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(bytes.clone()))
        .expect("live input allocation");
    let mut state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(memory.clone());
    state.record_population_storage_creation(base.block.clone());
    assert!(
        state
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .created_here(&base.block)
    );
    let replacement_bytes = MachineTerm::Variable(Variable(930_101));
    assert!(matches!(
        int32_continuity(
            &base,
            &bytes,
            &base,
            &replacement_bytes,
            &PureFactContext::new(),
        ),
        AllocationContinuity::Undecided(_)
    ));
    for output in [
        ResourceContext::new(),
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_allocation(
            base.clone(),
            replacement_bytes.clone(),
        )),
    ] {
        let (after_memory, _, retired) = apply_verified_heap_allocation_delta(
            memory.clone(),
            &memory,
            &input,
            &ResourceContext::new(),
            &output,
            &FunctionContractInterface::new(ProgramType::Void, vec![]),
            &PureFactContext::new(),
            None,
            &state,
            &state,
        )
        .expect("checked allocation retirement");
        assert_eq!(retired, vec![base.block.clone()]);
        let mut returned = state.clone().with_memory(after_memory);
        for block in retired {
            returned.retire_population_storage(&block).unwrap();
        }
        assert!(
            !returned
                .population_effects
                .creation
                .as_ref()
                .unwrap()
                .created_here(&base.block)
        );
    }
}

fn external_pointer(variable: u64) -> Pointer {
    Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(variable)), 4),
    }
}

#[test]
fn contract_allocation_retirement_respects_initialized_mutex_storage() {
    for continuity_undecided in [false, true] {
        let base = external_pointer(930_004);
        let bytes = MachineTerm::constant(48);
        let input = ResourceContext::new()
            .try_compose_with_fact(
                ResourceFact::own_allocation(base.clone(), bytes.clone()),
                &PureFactContext::new(),
            )
            .unwrap();
        let empty = ResourceContext::new();
        let output = if continuity_undecided {
            ResourceContext::new()
                .try_compose_with_fact(
                    ResourceFact::own_allocation(external_pointer(930_005), bytes.clone()),
                    &PureFactContext::new(),
                )
                .unwrap()
        } else {
            ResourceContext::new()
        };
        let interface = FunctionContractInterface::new(ProgramType::Void, vec![]);
        for mutex in [
            base.offset_by_bytes(8),
            Pointer::symbolic(Variable(930_006)),
        ] {
            let symbolic = matches!(mutex.block, PointerBlock::Symbolic(_));
            let state = super::super::mutexes::MutexContext::new(ExecutionState::new())
                .initialize_empty(mutex, 40)
                .unwrap()
                .into_state();
            let result = apply_verified_heap_allocation_delta(
                state.memory.clone(),
                &state.memory,
                &input,
                &empty,
                &output,
                &interface,
                &PureFactContext::new(),
                None,
                &state,
                &state,
            );
            if symbolic {
                assert!(matches!(
                    result,
                    Err(VerifiedAllocationDeltaError::Runtime(
                        RuntimeError::MutexStorageSeparationRequired { .. }
                    ))
                ));
            } else {
                assert!(matches!(
                    result,
                    Err(VerifiedAllocationDeltaError::Runtime(
                        RuntimeError::MutexStorageInUse { .. }
                    ))
                ));
            }
        }
    }
}

#[test]
fn continuity_requires_both_the_allocation_base_and_size() {
    let assumptions = PureFactContext::new();
    let input = external_pointer(930_000);
    assert_eq!(
        int32_continuity(
            &input,
            &MachineTerm::constant(4),
            &input,
            &MachineTerm::constant(4),
            &assumptions,
        ),
        AllocationContinuity::Same,
    );
    assert_eq!(
        int32_continuity(
            &input,
            &MachineTerm::constant(4),
            &input,
            &MachineTerm::constant(8),
            &assumptions,
        ),
        AllocationContinuity::Inconsistent,
    );
    assert_eq!(
        int32_continuity(
            &Pointer {
                block: PointerBlock::Heap(930_002),
                offset: PointerOffsetTerm::Constant(0),
            },
            &MachineTerm::constant(4),
            &Pointer {
                block: PointerBlock::Heap(930_003),
                offset: PointerOffsetTerm::Constant(0),
            },
            &MachineTerm::constant(4),
            &assumptions,
        ),
        AllocationContinuity::Distinct,
    );

    let other = external_pointer(930_001);
    assert_eq!(
        int32_continuity(
            &input,
            &MachineTerm::constant(4),
            &other,
            &MachineTerm::constant(4),
            &assumptions,
        ),
        AllocationContinuity::Undecided(ConditionTerm::pointer_equal(input, other)),
    );
}

#[test]
fn allocation_size_continuity_uses_graph_with_state_scope() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = crate::kernel::intern_memory(Memory::new().with_block("alloc-size", 8));
    let pointer = |index| Pointer {
        block: "alloc-size".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedMemory, index| {
        MachineTerm::Variable(crate::kernel::load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (
        MachineTerm::Variable(Variable(930_010)),
        MachineTerm::Variable(Variable(930_011)),
    );
    let after = crate::kernel::intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(MachineTerm::constant(9)),
    ));
    let size = |value| MachineTerm::add(value, MachineTerm::constant(1));
    let input_size = size(load(&before, a.clone()));
    let output_size = size(load(&before, b.clone()));
    let later_size = size(load(&after, b.clone()));
    let base = external_pointer(930_012);
    let premise = ConditionTerm::equal(a, b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();

    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert_eq!(
        int32_continuity(&base, &input_size, &base, &output_size, &branch),
        AllocationContinuity::Same,
    );
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    for (size, context) in [(&later_size, &branch), (&output_size, &parent)] {
        assert!(matches!(
            int32_continuity(&base, &input_size, &base, size, context),
            AllocationContinuity::Undecided(ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: _,
                right: _
            }),
        ));
    }
    assert_ne!(
        int32_continuity(
            &base,
            &input_size,
            &external_pointer(930_013),
            &output_size,
            &branch
        ),
        AllocationContinuity::Same,
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/allocation_continuity_tests.rs");
}

/// A contract's `uint64` `allocation` byte count is a 64-bit extent only
/// under `malloc`'s decision (`design/heap-extents.md`, stage 3): a product
/// `n * 4u64` needs `1 <= n <= PTRDIFF_MAX / 4` decided, a product of two
/// symbolic factors is never one, and a constant that fits a 32-bit extent is
/// that extent. A clause already established elsewhere (a contract's own
/// entry clause, a held body) is assumed.
#[test]
fn a_contract_uint64_allocation_extent_needs_the_no_wrap_decision() {
    let count = MachineTerm::Variable(Variable(930_300));
    let other = MachineTerm::Variable(Variable(930_301));
    let product = MachineTerm::uint64_multiply(count.clone(), MachineTerm::uint64_constant(4));
    let unbounded = PureFactContext::new();
    let bounded = [
        ConditionTerm::uint64_greater_than(count.clone(), MachineTerm::uint64_constant(0)),
        ConditionTerm::uint64_less_equal(count.clone(), MachineTerm::uint64_constant(1000)),
        ConditionTerm::uint64_greater_than(other.clone(), MachineTerm::uint64_constant(0)),
        ConditionTerm::uint64_less_equal(other.clone(), MachineTerm::uint64_constant(1000)),
    ]
    .into_iter()
    .fold(PureFactContext::new(), |context, condition| {
        context.assume_condition(condition, true)
    });

    assert_eq!(
        uint64_allocation_extent_argument(&MachineTerm::uint64_constant(16), &unbounded),
        Ok(ProgramValue::Int32(MachineTerm::constant(16))),
    );
    assert!(matches!(
        uint64_allocation_extent_argument(&product, &unbounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
    assert_eq!(
        uint64_allocation_extent_argument(&product, &bounded),
        Ok(ProgramValue::UInt64(product.clone())),
    );
    assert_eq!(
        uint64_allocation_extent_argument(
            &product,
            &unbounded.clone().assume_entry_clause_extents()
        ),
        Ok(ProgramValue::UInt64(product.clone())),
    );
    let symbolic_product = MachineTerm::uint64_multiply(count.clone(), other);
    assert!(matches!(
        uint64_allocation_extent_argument(&symbolic_product, &bounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
    assert!(matches!(
        uint64_allocation_extent_argument(&MachineTerm::uint64_constant(0), &unbounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
    assert!(matches!(
        uint64_allocation_extent_argument(&MachineTerm::uint64_constant(u64::MAX), &unbounded),
        Err(RuntimeError::FunctionContract(_)),
    ));
}
