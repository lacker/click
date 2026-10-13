//! Shared, dependency-closed certificates for successive complete pointer reads.

use super::*;
use crate::kernel::resource_tracker::cell_source::{CellLookupGuard, MemoryDagHopJustification};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, Weak};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct PointerFrameEquality {
    left: OriginLoadEndpoint,
    right: OriginLoadEndpoint,
    left_projection: Option<CanonicalLoadProjectionEvidence>,
    right_projection: Option<CanonicalLoadProjectionEvidence>,
    prefix: Arc<PointerFramePrefix>,
    reversed: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PointerFramePrefix {
    pointer: Pointer,
    oldest: SharedCMemory,
    current: SharedCMemory,
    supports: Arc<Vec<Proposition>>,
    step: Option<PointerFrameStep>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct PointerFrameStep {
    derivation: Arc<CMemoryDerivation>,
    justification: MemoryDagHopJustification,
    premises: RetainedPremises,
    parent: Arc<PointerFramePrefix>,
}

type PrefixKey = ((u32, u32), (u32, u32), Pointer);

thread_local! {
    // Strong entries share only selected immutable evidence, never a caller
    // context. The session reset and the existing provenance bound cap them.
    static PREFIXES: RefCell<HashMap<PrefixKey, Arc<PointerFramePrefix>>> = RefCell::new(HashMap::new());
    // A positive check is against the node's own exact retained premises.
    // Weak identity excludes address reuse and mutation via Arc::make_mut.
    static CHECKED_PREFIXES: RefCell<HashMap<usize, Weak<PointerFramePrefix>>> = RefCell::new(HashMap::new());
}

pub(super) fn clear_memos() {
    PREFIXES.with(|memo| memo.borrow_mut().clear());
    CHECKED_PREFIXES.with(|memo| memo.borrow_mut().clear());
}

fn supports_available(prefix: &PointerFramePrefix, context: &PureFactContext) -> bool {
    prefix.supports.iter().all(|premise| {
        crate::instrumentation::record_deterministic_work(1);
        context.contains_assumed_exact(premise)
    })
}

fn checked(prefix: &Arc<PointerFramePrefix>) -> bool {
    let mut current = prefix.clone();
    let mut pending = Vec::new();
    loop {
        crate::instrumentation::record_deterministic_work(1);
        let key = Arc::as_ptr(&current) as usize;
        if CHECKED_PREFIXES.with(|memo| {
            memo.borrow()
                .get(&key)
                .and_then(Weak::upgrade)
                .is_some_and(|known| Arc::ptr_eq(&known, &current))
        }) {
            break;
        }
        let Some(step) = &current.step else {
            if current.oldest.arena_id() != current.current.arena_id()
                || !current.supports.is_empty()
            {
                return false;
            }
            pending.push(current);
            break;
        };
        if step.parent.pointer != current.pointer
            || step.parent.oldest.arena_id() != current.oldest.arena_id()
            || step.derivation.base().arena_id() != step.parent.current.arena_id()
            || step.parent.current.arena_id() >= current.current.arena_id()
            || current.current.derivation().as_deref() != Some(step.derivation.as_ref())
            || !step.justification.is_typed()
            || !step
                .premises
                .named()
                .iter()
                .all(|premise| current.supports.binary_search(premise).is_ok())
            || !step
                .parent
                .supports
                .iter()
                .all(|premise| current.supports.binary_search(premise).is_ok())
        {
            return false;
        }
        let parent = step.parent.clone();
        pending.push(current);
        current = parent;
    }
    for current in pending.into_iter().rev() {
        if let Some(step) = &current.step
            && !step.justification.checks(
                &step.derivation,
                &current.pointer,
                C_POINTER_BYTE_WIDTH,
                &step.premises.context(),
            )
        {
            return false;
        }
        CHECKED_PREFIXES.with(|memo| {
            let mut memo = memo.borrow_mut();
            if memo.len() >= DAG_LOAD_EQUALITY_MEMO_LIMIT {
                memo.clear();
            }
            memo.insert(Arc::as_ptr(&current) as usize, Arc::downgrade(&current));
        });
    }
    true
}

fn joined_supports(parent: &Arc<Vec<Proposition>>, own: &[Proposition]) -> Arc<Vec<Proposition>> {
    if own
        .iter()
        .all(|premise| parent.binary_search(premise).is_ok())
    {
        crate::instrumentation::record_deterministic_work(own.len());
        return parent.clone();
    }
    let mut joined = BTreeSet::new();
    for premise in parent.iter().chain(own) {
        crate::instrumentation::record_deterministic_work(1);
        joined.insert(premise.clone());
    }
    Arc::new(joined.into_iter().collect())
}

fn build_prefix(
    newest: &SharedCMemory,
    oldest: &SharedCMemory,
    pointer: &Pointer,
    context: &PureFactContext,
) -> Option<Arc<PointerFramePrefix>> {
    let epoch = crate::kernel::assumptions::incomplete_reasoning_epoch();
    let refusals = crate::kernel::resource_tracker::cell_source::memory_dag_cell_lookup_refusals();
    let mut current = newest.clone();
    let mut pending = Vec::new();
    let mut parent = loop {
        crate::instrumentation::record_deterministic_work(1);
        if current.arena_id() == oldest.arena_id() {
            break Arc::new(PointerFramePrefix {
                pointer: pointer.clone(),
                oldest: oldest.clone(),
                current,
                supports: Arc::new(Vec::new()),
                step: None,
            });
        }
        if current.arena_id() < oldest.arena_id() {
            return None;
        }
        let key = (oldest.arena_id(), current.arena_id(), pointer.clone());
        let cached = PREFIXES.with(|memo| memo.borrow().get(&key).cloned());
        if let Some(cached) = cached
            && supports_available(&cached, context)
            && checked(&cached)
        {
            break cached;
        }
        let _lookup = CellLookupGuard::enter(&current, pointer)?;
        let derivation = current.derivation()?;
        if derivation.base().arena_id() >= current.arena_id() {
            return None;
        }
        let (effect, premises) = crate::kernel::assumptions::collect_reasoning_provenance(|| {
            crate::kernel::assumptions::capture_implicit_reasoning_provenance(|| {
                crate::kernel::resource_tracker::step_effect::affects(
                    &derivation,
                    &current,
                    crate::kernel::resource_tracker::Resource::Cell {
                        pointer,
                        bytes: C_POINTER_BYTE_WIDTH,
                    },
                    &crate::kernel::resource_tracker::step_effect::Evidence {
                        assumptions: context,
                        cross_loop_havoc: true,
                    },
                )
            })
        });
        let crate::kernel::resource_tracker::step_effect::StepEffect::Separate(
            crate::kernel::resource_tracker::step_effect::Separation::Cell(justification),
        ) = effect
        else {
            return None;
        };
        if !justification.is_typed() {
            return None;
        }
        let detached = premises
            .iter()
            .fold(PureFactContext::new(), |facts, premise| {
                facts.assume_proposition(premise.clone())
            });
        // Checking in the detached cited context establishes that the edge
        // has no unrecorded dependence on the source's other assumptions.
        if !justification.checks(&derivation, pointer, C_POINTER_BYTE_WIDTH, &detached) {
            return None;
        }
        let retained = RetainedPremises::from_context(&detached);
        let base = derivation.base().clone();
        pending.push((current, derivation, justification, retained));
        current = base;
    };
    let mut new_nodes = Vec::new();
    for (current, derivation, justification, premises) in pending.into_iter().rev() {
        parent = Arc::new(PointerFramePrefix {
            pointer: pointer.clone(),
            oldest: oldest.clone(),
            current,
            supports: joined_supports(&parent.supports, premises.named()),
            step: Some(PointerFrameStep {
                derivation,
                justification,
                premises,
                parent,
            }),
        });
        if !checked(&parent) {
            return None;
        }
        new_nodes.push(parent.clone());
    }
    if epoch != crate::kernel::assumptions::incomplete_reasoning_epoch()
        || refusals
            != crate::kernel::resource_tracker::cell_source::memory_dag_cell_lookup_refusals()
    {
        return None;
    }
    PREFIXES.with(|memo| {
        let mut memo = memo.borrow_mut();
        if memo.len() + new_nodes.len() >= DAG_LOAD_EQUALITY_MEMO_LIMIT {
            memo.clear();
        }
        for prefix in new_nodes {
            memo.insert(
                (
                    oldest.arena_id(),
                    prefix.current.arena_id(),
                    pointer.clone(),
                ),
                prefix,
            );
        }
    });
    Some(parent)
}

impl PointerFrameEquality {
    pub(super) fn for_terms(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        context: &PureFactContext,
    ) -> Option<Self> {
        if !crate::kernel::resource_tracker::cell_source::memory_dag_cell_lookup_depth_is_zero()
            || origin_load_width(left) != Some(C_POINTER_BYTE_WIDTH)
            || origin_load_width(right) != Some(C_POINTER_BYTE_WIDTH)
        {
            return None;
        }
        let left = OriginLoadEndpoint::for_named_term(left)?;
        let right = OriginLoadEndpoint::for_named_term(right)?;
        if left.kind != LoadKind::Pointer
            || right.kind != LoadKind::Pointer
            || left.pointer != right.pointer
        {
            return None;
        }
        let left_projection =
            CanonicalLoadProjectionEvidence::for_endpoint(&left.memory, &left.pointer);
        let right_projection =
            CanonicalLoadProjectionEvidence::for_endpoint(&right.memory, &right.pointer);
        let left_source = left_projection.as_ref().map_or(&left.memory, |p| &p.source);
        let right_source = right_projection
            .as_ref()
            .map_or(&right.memory, |p| &p.source);
        if left_source.arena_id() == right_source.arena_id() {
            return None;
        }
        let reversed = left_source.arena_id() < right_source.arena_id();
        let (newest, oldest) = if reversed {
            (right_source, left_source)
        } else {
            (left_source, right_source)
        };
        let prefix = build_prefix(newest, oldest, &left.pointer, context)?;
        Some(Self {
            left,
            right,
            left_projection,
            right_projection,
            prefix,
            reversed,
        })
    }

    pub(super) fn checks(
        &self,
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        context: &PureFactContext,
    ) -> bool {
        if origin_load_width(left) != Some(C_POINTER_BYTE_WIDTH)
            || origin_load_width(right) != Some(C_POINTER_BYTE_WIDTH)
            || OriginLoadEndpoint::for_named_term(left).as_ref() != Some(&self.left)
            || OriginLoadEndpoint::for_named_term(right).as_ref() != Some(&self.right)
            || self.left.kind != LoadKind::Pointer
            || self.right.kind != LoadKind::Pointer
            || self.left.pointer != self.right.pointer
            || self.prefix.pointer != self.left.pointer
        {
            return false;
        }
        let endpoint =
            |load: &OriginLoadEndpoint, projection: &Option<CanonicalLoadProjectionEvidence>| {
                match projection {
                    None => Some(load.memory.clone()),
                    Some(projection) => projection
                        .checks(&load.memory, &load.pointer)
                        .then(|| projection.source.clone()),
                }
            };
        let Some(left_source) = endpoint(&self.left, &self.left_projection) else {
            return false;
        };
        let Some(right_source) = endpoint(&self.right, &self.right_projection) else {
            return false;
        };
        let (newest, oldest) = if self.reversed {
            (right_source, left_source)
        } else {
            (left_source, right_source)
        };
        self.prefix.current.arena_id() == newest.arena_id()
            && self.prefix.oldest.arena_id() == oldest.arena_id()
            && supports_available(&self.prefix, context)
            && checked(&self.prefix)
    }

    pub(super) fn record_provenance(&self, context: &PureFactContext) {
        for premise in self.prefix.supports.iter() {
            crate::kernel::record_implicit_reasoning_provenance(context, premise);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::int32;

    fn fixture() -> (
        PureFactContext,
        CMemory,
        CMemory,
        Pointer,
        CMemoryRange,
        Proposition,
    ) {
        let address = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let write = Pointer {
            block: address.block.clone(),
            offset: PointerOffsetTerm::Variable(Variable(998_001)),
        };
        let written = CMemoryRange::new_with_element_width(write, 0u32.into(), 1u32.into(), 4);
        let separation = Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                address.clone(),
                0u32.into(),
                1u32.into(),
                8,
            ))),
            right: Box::new(CResource::Memory(written.clone())),
        };
        let context = PureFactContext::new().assume_proposition(separation.clone());
        let before = CMemory::new();
        let after = before.clone().with_call_memory_havoc(
            Variable(998_002),
            std::slice::from_ref(&written),
            &context,
            None,
        );
        (context, before, after, address, written, separation)
    }

    fn load(memory: &CMemory, address: &Pointer) -> Bitvector32Term {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(address.clone()),
            LoadKind::Pointer,
        )
    }

    fn frame(
        left: &Bitvector32Term,
        right: &Bitvector32Term,
        context: &PureFactContext,
    ) -> Option<PointerFrameEquality> {
        let previous = EXPLICIT_DAG_CHECK.with(|flag| flag.replace(true));
        let result =
            with_extended_dag_bridging(|| PointerFrameEquality::for_terms(left, right, context));
        EXPLICIT_DAG_CHECK.with(|flag| flag.set(previous));
        result
    }

    #[test]
    fn shared_pointer_frame_checks_named_authority_and_mutated_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let (context, before, after, address, written, separation) = fixture();
        let left = load(&after, &address);
        let right = load(&before, &address);
        let proof = frame(&left, &right, &context).expect("a complete separated pointer frame");
        assert!(proof.prefix.supports.contains(&separation));
        assert!(proof.checks(&left, &right, &context));
        let capture = crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start();
        assert!(checked_recorded_atomic_load_equality(
            &left, &right, &context
        ));
        let captured = capture.finish();
        assert!(captured.iter().any(|proof| matches!(
            proof.evidence,
            CheckedLoadEqualityEvidence::SharedPointerFrame(_)
        )));
        assert!(captured.iter().all(|proof| proof.checks(&context)));
        let withdrawn = context.without_exact_fact(&separation);
        assert!(!proof.checks(&left, &right, &withdrawn));
        assert!(frame(&left, &right, &withdrawn).is_none());
        assert!(captured.iter().all(|proof| !proof.checks(&withdrawn)));

        let unrelated = context.clone().assume_condition(
            ConditionTerm::equal(Bitvector32Term::Variable(Variable(998_003)), 0u32.into()),
            true,
        );
        assert!(proof.checks(&left, &right, &unrelated));
        let wrong_cell = load(&after, &address.offset_by_bytes(8));
        assert!(!proof.checks(&wrong_cell, &right, &context));
        assert!(frame(&wrong_cell, &right, &context).is_none());
        let Bitvector32Term::MemoryLoad(memory, pointer, _) = &left else {
            unreachable!();
        };
        let narrow = Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone(), LoadKind::Bits32);
        assert!(!proof.checks(&narrow, &right, &context));
        assert!(frame(&narrow, &right, &context).is_none());
        let partial_variable =
            crate::kernel::eval::load_variable_for_exact_cell(memory, pointer, LoadKind::Bits32, 4);
        let partial = Bitvector32Term::Variable(partial_variable);
        assert_eq!(origin_load_width(&partial), Some(4));
        assert!(frame(&partial, &right, &context).is_none());
        assert!(!proof.checks(&partial, &right, &context));
        let complete_variable = crate::kernel::eval::load_variable_for_exact_cell(
            memory,
            pointer,
            LoadKind::Pointer,
            4,
        );
        assert_eq!(
            origin_load_width(&Bitvector32Term::Variable(complete_variable)),
            Some(8)
        );
        let foreign = before.clone().with_block("global:frame-foreign", 4);
        assert!(!proof.checks(&left, &load(&foreign, &address), &context));

        // Changing an Arc-backed node cannot reuse the checked weak identity.
        let mut missing_supports = proof.clone();
        Arc::make_mut(&mut missing_supports.prefix).supports = Arc::new(Vec::new());
        assert!(!missing_supports.checks(&left, &right, &context));
        let mut missing_edge_premise = proof.clone();
        Arc::make_mut(&mut missing_edge_premise.prefix)
            .step
            .as_mut()
            .unwrap()
            .premises = RetainedPremises::from_context(&PureFactContext::new());
        assert!(!missing_edge_premise.checks(&left, &right, &context));

        let overlapping = after.clone().store(address.offset_by_bytes(4), int32(3));
        assert!(frame(&load(&overlapping, &address), &right, &context).is_none());
        let too_wide = CMemoryRange::new_with_element_width(
            written.base().clone(),
            0u32.into(),
            2u32.into(),
            4,
        );
        let wider = after.with_call_memory_havoc(
            Variable(998_004),
            std::slice::from_ref(&too_wide),
            &context,
            None,
        );
        assert!(frame(&load(&wider, &address), &right, &context).is_none());
    }
}
