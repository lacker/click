//! Access observations belong to read descriptors, not reserved variable names.
//! Capture/restore shares persistent roots; selected shared reads use an ID lookup.
use super::*;

type Key = ((u32, u32), Pointer, LoadKind);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(super) struct Id(u64);

#[derive(Clone)]
struct Record {
    memory: SharedMemory,
    pointer: Pointer,
    kind: LoadKind,
    origin: SharedMemory,
    epoch: u64,
    bytes: u32,
    typed: bool,
    selected: bool,
}

#[derive(Clone, Default)]
pub(super) struct State {
    next: u64,
    keys: imbl::HashMap<Key, Id>,
    records: imbl::HashMap<Id, Record>,
    terms: imbl::HashMap<u64, Id>,
    latest: imbl::HashMap<(u64, Id), (SharedMemory, Pointer)>,
}

thread_local! {
    static STATE: std::cell::RefCell<State> = Default::default();
}

pub(super) fn capture() -> State {
    STATE.with(|state| state.borrow().clone())
}

pub(super) fn restore(saved: &State) {
    STATE.with(|state| *state.borrow_mut() = saved.clone());
}

pub(super) fn clear() {
    STATE.with(|state| *state.borrow_mut() = State::default());
}

pub(super) fn existing(memory: &SharedMemory, pointer: &Pointer, kind: LoadKind) -> Option<Id> {
    crate::instrumentation::record_deterministic_work(1);
    STATE.with(|state| {
        state
            .borrow()
            .keys
            .get(&(memory.arena_id(), pointer.clone(), kind))
            .copied()
    })
}

pub(super) fn record(
    memory: &SharedMemory,
    pointer: &Pointer,
    kind: LoadKind,
    origin: &SharedMemory,
    bytes: u32,
) -> Id {
    record_with_width(memory, pointer, kind, origin, bytes, true)
}

pub(super) fn record_untyped(
    memory: &SharedMemory,
    pointer: &Pointer,
    kind: LoadKind,
    origin: &SharedMemory,
) -> Id {
    record_with_width(
        memory,
        pointer,
        kind,
        origin,
        kind.unrecorded_access_byte_width(),
        false,
    )
}

fn record_with_width(
    memory: &SharedMemory,
    pointer: &Pointer,
    kind: LoadKind,
    origin: &SharedMemory,
    bytes: u32,
    typed: bool,
) -> Id {
    crate::instrumentation::record_deterministic_work(1);
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        let mut state = state.borrow_mut();
        let key = (memory.arena_id(), pointer.clone(), kind);
        if let Some(id) = state.keys.get(&key).copied() {
            refresh_record(
                state.records.get_mut(&id).expect("recorded read"),
                origin,
                epoch,
                bytes,
                typed,
            );
            return id;
        }
        let id = Id(state.next);
        state.next = state
            .next
            .checked_add(1)
            .expect("read observation ID overflow");
        state.keys.insert(key, id);
        state.records.insert(
            id,
            Record {
                memory: memory.clone(),
                pointer: pointer.clone(),
                kind,
                origin: origin.clone(),
                epoch,
                bytes,
                typed,
                selected: false,
            },
        );
        id
    })
}

fn refresh_record(record: &mut Record, origin: &SharedMemory, epoch: u64, bytes: u32, typed: bool) {
    let first_typed = typed && !record.typed;
    if first_typed {
        record.bytes = bytes;
    } else if typed {
        record.bytes = record.bytes.max(bytes);
    }
    record.typed |= typed;
    if record.epoch != epoch || first_typed {
        record.origin = origin.clone();
        record.epoch = epoch;
    }
}

pub(super) fn select(id: Id) {
    STATE.with(|state| {
        state
            .borrow_mut()
            .records
            .get_mut(&id)
            .expect("recorded read")
            .selected = true
    });
}

pub(super) fn selected(memory: &SharedMemory, pointer: &Pointer, kind: LoadKind) -> bool {
    existing(memory, pointer, kind).is_some_and(|id| {
        STATE.with(|state| {
            state
                .borrow()
                .records
                .get(&id)
                .is_some_and(|read| read.selected)
        })
    })
}

pub(super) fn refresh(id: Id, origin: &SharedMemory, bytes: u32) {
    crate::instrumentation::record_deterministic_work(1);
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        refresh_record(
            state
                .borrow_mut()
                .records
                .get_mut(&id)
                .expect("registered read observation"),
            origin,
            epoch,
            bytes,
            true,
        )
    });
}

pub(super) fn produced(read: &MachineTerm, source: &MachineTerm) {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = read else {
        return;
    };
    let MachineTerm::MemoryLoad(origin, address, _) = source else {
        return;
    };
    if *kind != LoadKind::Bits64 {
        return;
    }
    let Some(id) = existing(memory, pointer, *kind) else {
        return;
    };
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        state
            .borrow_mut()
            .latest
            .insert((epoch, id), (origin.clone(), address.as_ref().clone()));
    });
}

pub(super) fn latest(read: &MachineTerm) -> Option<MachineTerm> {
    let MachineTerm::MemoryLoad(memory, pointer, kind) = read else {
        return None;
    };
    let id = existing(memory, pointer, *kind)?;
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        state
            .borrow()
            .latest
            .get(&(epoch, id))
            .map(|(memory, pointer)| {
                MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), *kind)
            })
    })
}

pub(super) fn remember_term(term: &crate::kernel::KernelTerm, id: Id) {
    STATE.with(|state| {
        state.borrow_mut().terms.insert(term.id(), id);
    });
}

pub(super) fn bytes(id: Id) -> Option<u32> {
    STATE.with(|state| {
        state
            .borrow()
            .records
            .get(&id)
            .filter(|record| record.typed)
            .map(|record| record.bytes)
    })
}

pub(super) fn observation(id: Id) -> Option<ScalarReadObservation> {
    crate::instrumentation::record_deterministic_work(1);
    let epoch = LOAD_ORIGIN_EPOCH.with(std::cell::Cell::get);
    STATE.with(|state| {
        state
            .borrow()
            .records
            .get(&id)
            .map(|record| ScalarReadObservation {
                memory: record.memory.clone(),
                pointer: record.pointer.clone(),
                kind: record.kind,
                bytes: record.bytes,
                origin: (record.epoch == epoch).then(|| record.origin.clone()),
            })
    })
}

pub(super) fn for_operand(
    operand: crate::kernel::MachineOperandView<'_>,
) -> Option<ScalarReadObservation> {
    use crate::kernel::MachineOperandView;
    if let Some(variable) = operand.variable() {
        let id = LOAD_VARIABLE_REGISTRY
            .with(|registry| registry.borrow().get(variable).map(|read| read.observation))?;
        return observation(id);
    }
    if let MachineOperandView::Shared(term) = operand
        && let Some(id) = STATE.with(|state| state.borrow().terms.get(&term.id()).copied())
    {
        return observation(id);
    }
    let (memory, pointer, kind) = operand.read()?;
    // Inspection is not an access observation. In particular, retaining the
    // conservative width of an unseen descriptor would widen a later typed
    // producer, and retaining this state would steal its first live origin.
    let Some(id) = existing(memory, pointer, kind) else {
        return Some(ScalarReadObservation {
            memory: memory.clone(),
            pointer: pointer.clone(),
            kind,
            bytes: load_term_access_width(memory, pointer, kind),
            origin: Some(memory.clone()),
        });
    };
    if let MachineOperandView::Shared(term) = operand {
        remember_term(term, id);
    }
    observation(id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTerm, MachineOperandView, VerificationSession};

    #[test]
    fn a_typed_producer_replaces_an_untyped_canonical_reads_guessed_width() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(Memory::new());
        let pointer = Pointer::symbolic(Variable(998_709));
        let untyped = canonical_scalar_read(&MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        ));
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&untyped))
                .unwrap()
                .bytes,
            8
        );
        record_load_access_width(memory.memory(), &pointer, 4);
        let typed = canonical_scalar_read(&MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        ));
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&typed))
                .unwrap()
                .bytes,
            4
        );
        // A genuine wider observation remains conservative when a narrower
        // producer later names the same descriptor.
        let MachineTerm::MemoryLoad(selected, address, kind) = &typed else {
            unreachable!()
        };
        record(selected, address, *kind, &memory, 8);
        record(selected, address, *kind, &memory, 4);
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&typed))
                .unwrap()
                .bytes,
            8
        );
    }

    #[test]
    fn inspecting_an_unobserved_read_does_not_capture_its_width_or_origin() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(Memory::new());
        let pointer = Pointer::symbolic(Variable(998_707));
        let read =
            MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Int32);
        assert_eq!(
            for_operand(MachineOperandView::Legacy(&read))
                .unwrap()
                .bytes,
            8
        );
        assert!(existing(&memory, &pointer, LoadKind::Int32).is_none());
        let live = intern_memory(memory.memory().clone().store(
            pointer.offset_by_bytes(16),
            ProgramValue::Int32(1u32.into()),
        ));
        record(&memory, &pointer, LoadKind::Int32, &live, 4);
        let observed = for_operand(MachineOperandView::Legacy(&read)).unwrap();
        assert_eq!(observed.bytes, 4);
        assert_eq!(observed.origin, Some(live));
    }

    fn cyclic_frame_read(index: u64) -> (Proposition, Variable) {
        let pointer = Pointer {
            block: format!("local:frame-origin-{index}").into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = intern_memory(Memory::new().with_block(pointer.block.clone(), 4));
        let read =
            MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), LoadKind::Int32);
        let bound = Variable(998_800 + index);
        let range = MemoryRange::new_with_element_width(
            Pointer {
                block: "frame-target".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            0u32.into(),
            MachineTerm::add_at(
                MachineIntegerType::Int32,
                read.clone(),
                MachineTerm::Variable(bound),
            ),
            4,
        );
        let origin = intern_memory(memory.memory().clone().with_call_memory_havoc(
            Variable(999_800 + index),
            &[range],
            &PureFactContext::new(),
            None,
        ));
        // The local read survives a havoc of another block. Its live origin
        // contains a range bound that refers to the same structural version.
        record(&memory, &pointer, LoadKind::Int32, &origin, 4);
        (
            Proposition::ConditionIs(ConditionTerm::equal(read, 0u32.into()), true),
            bound,
        )
    }

    #[test]
    fn frame_collection_terminates_on_cyclic_observation_origins_and_keeps_bounds() {
        let _session = VerificationSession::enter();
        let (proposition, bound) = cyclic_frame_read(0);
        let collect = || {
            let mut variables = std::collections::BTreeSet::new();
            crate::kernel::reasoning::variable_collection::collect_proposition_frame_variables(
                &proposition,
                &mut variables,
            );
            variables
        };
        let first = collect();
        assert!(first.contains(&bound));
        assert_eq!(collect(), first, "visited states belong to one collection");
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[test]
    fn structural_observations_need_no_reserved_name_and_restore_branch_metadata() {
        let _session = VerificationSession::enter();
        let memory = intern_memory(Memory::new());
        let pointer = Pointer::symbolic(Variable(998_701));
        let read = KernelTerm::scalar_read_descriptor(
            MachineIntegerType::Int32,
            &memory,
            &pointer,
            LoadKind::Int32,
        )
        .unwrap();
        let id = record(&memory, &pointer, LoadKind::Int32, &memory, 4);
        remember_term(&read, id);
        let observe = |read: &KernelTerm| for_operand(MachineOperandView::Shared(read)).unwrap();
        assert_eq!(load_variable_registry_len(), 0);
        assert_eq!(observe(&read).bytes, 4);
        let other_format = read.with_machine_observation_type(MachineIntegerType::UInt32);
        assert_eq!(observe(&other_format).bytes, 4);
        let saved = capture_load_variable_registry();
        begin_load_origin_epoch();
        assert!(observe(&other_format).origin.is_none());
        let later = intern_memory(memory.memory().clone().store(
            pointer.offset_by_bytes(16),
            ProgramValue::Int32(1u32.into()),
        ));
        record(&memory, &pointer, LoadKind::Int32, &later, 8);
        assert_eq!(observe(&read).bytes, 8);
        assert_eq!(observe(&other_format).origin, Some(later));
        restore_load_variable_registry(&saved);
        assert_eq!(observe(&read).bytes, 4);
        assert_eq!(observe(&other_format).origin, Some(memory));
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[test]
    fn structural_observations_distinguish_read_kind_and_state() {
        let _session = VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(998_702));
        let before = intern_memory(Memory::new());
        let after =
            intern_memory(Memory::new().store(pointer.clone(), ProgramValue::Int32(1u32.into())));
        let first = record(&before, &pointer, LoadKind::Int32, &before, 4);
        let other_kind = record(&before, &pointer, LoadKind::Int16, &before, 2);
        let other_time = record(&after, &pointer, LoadKind::Int32, &after, 8);
        assert_ne!(first, other_kind);
        assert_ne!(first, other_time);
        assert_eq!(bytes(first), Some(4));
        assert_eq!(bytes(other_kind), Some(2));
        assert_eq!(bytes(other_time), Some(8));
        let narrow_access = record(
            &before,
            &pointer.offset_by_bytes(16),
            LoadKind::Int32,
            &before,
            2,
        );
        assert_eq!(bytes(narrow_access), Some(2));
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[test]
    fn ordinary_integer_producers_retain_reads_without_reserved_variables() {
        let _session = VerificationSession::enter();
        let memory = Memory::new();
        let pointer = Pointer::symbolic(Variable(998_704));
        for ty in [
            ProgramType::Int8,
            ProgramType::UInt8,
            ProgramType::Int16,
            ProgramType::UInt16,
            ProgramType::Int32,
            ProgramType::UInt32,
            ProgramType::Int64,
            ProgramType::UInt64,
            ProgramType::Int128,
            ProgramType::UInt128,
        ] {
            let mut facts = ExecutionFacts::new();
            let value = canonicalized_symbolic_load_value_with_identity(
                &memory,
                &pointer,
                ty,
                &mut facts,
                &PureFactContext::new(),
                None,
                LoadPurpose::Logical,
            )
            .expect("integer read");
            let read =
                crate::kernel::spec::program_value_bitvector_term(&value).expect("scalar term");
            let MachineTerm::MemoryLoad(retained_state, address, kind) = &read else {
                panic!("{ty:?} must retain its read: {read:?}");
            };
            assert_eq!(address.as_ref(), &pointer);
            assert_eq!(
                canonical_form_of_load(retained_state.clone(), pointer.clone(), *kind),
                read
            );
            assert!(facts.is_empty());
            assert_eq!(load_variable_registry_len(), 0);
        }
    }

    #[test]
    fn selecting_a_read_keeps_its_address_when_another_read_was_stored_there() {
        let _session = VerificationSession::enter();
        let source = Pointer::symbolic(Variable(998_705));
        let destination = Pointer::symbolic(Variable(998_706));
        let memory = intern_memory(Memory::new());
        let held = canonical_form_of_load(memory.clone(), source, LoadKind::Int32);
        let after = intern_memory(
            memory
                .memory()
                .clone()
                .store(destination.clone(), ProgramValue::Int32(held.clone())),
        );
        let read = canonical_form_of_load(after, destination.clone(), LoadKind::Int32);
        assert!(
            matches!(&read, MachineTerm::MemoryLoad(_, pointer, LoadKind::Int32) if **pointer == destination)
        );
        assert_ne!(read, held);
        assert_eq!(read_over_write_value(&read), Some(held));
        assert_eq!(load_variable_registry_len(), 0);
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/eval/memory_loads/read_observations/tests.rs");
    }
}
