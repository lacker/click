//! Producer observations connecting locked MIR operations to completed
//! reference assignments and checked memory accesses. Observation labels grant
//! no permission; optional checked lease plans are separate semantic operations.
use super::*;
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use std::sync::Arc;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ReferenceBorrowSourceId {
    pub(crate) import_identity: Arc<str>,
    pub(crate) function: Arc<str>,
    pub(crate) block: usize,
    pub(crate) statement: usize,
    pub(crate) parent: Arc<str>,
    pub(crate) child: Arc<str>,
}

/// Source observations compare neutrally. A checked lease plan participates in
/// statement identity and executes an actual checked birth.
#[derive(Clone, Debug, Default)]
pub struct StatementAssignSource(
    Option<Arc<ReferenceBorrowSourceId>>,
    Option<Arc<ScalarReferenceSourcePlan>>,
);
impl StatementAssignSource {
    pub(crate) fn new(source: ReferenceBorrowSourceId) -> Self {
        Self(Some(Arc::new(source)), None)
    }
    pub(crate) fn as_ref(&self) -> Option<&ReferenceBorrowSourceId> {
        self.0.as_deref()
    }
    pub(crate) fn with_lease_plan(mut self, plan: Arc<ScalarReferenceSourcePlan>) -> Self {
        self.1 = Some(plan);
        self
    }
    pub(super) fn lease_plan(&self) -> Option<&Arc<ScalarReferenceSourcePlan>> {
        self.1.as_ref()
    }
    fn semantic_key(&self) -> Option<&ScalarReferencePlanKey> {
        self.1.as_ref().map(|plan| plan.key())
    }
    pub(super) fn completed(
        &self,
        before: &ExecutionState,
        after: &ExecutionState,
        assigned: &str,
    ) -> Option<ExecutionPureFact> {
        let source = self.0.as_ref()?;
        if assigned != source.child.as_ref() {
            return None;
        }
        let ProgramValue::Pointer(parent) = before.locals.get(&source.parent)?.native_payload()?
        else {
            return None;
        };
        let ProgramValue::Pointer(child) = after.locals.get(&source.child)?.native_payload()?
        else {
            return None;
        };
        if parent.pointer() != child.pointer() || parent.program_type() != child.program_type() {
            return None;
        }
        let mut fact = ExecutionPureFact::certified(Proposition::ConditionIs(
            ConditionTerm::PointerEqual(
                Box::new(parent.pointer().clone()),
                Box::new(child.pointer().clone()),
            ),
            true,
        ));
        fact.public = false;
        fact.logical_read_equation = true;
        fact.reference_observation = ReferenceObservationSource(Some(Arc::new(
            ReferenceObservation::Borrow(ReferenceBorrowObservation {
                source: source.clone(),
                pointer: child.pointer().clone(),
            }),
        )));
        Some(fact)
    }
}
impl PartialEq for StatementAssignSource {
    fn eq(&self, other: &Self) -> bool {
        self.semantic_key() == other.semantic_key()
    }
}
impl Eq for StatementAssignSource {}
impl std::hash::Hash for StatementAssignSource {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.semantic_key(), state);
    }
}
impl Ord for StatementAssignSource {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.semantic_key().cmp(&other.semantic_key())
    }
}
impl PartialOrd for StatementAssignSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Debug)]
struct ReferenceBorrowObservation {
    source: Arc<ReferenceBorrowSourceId>,
    pointer: Pointer,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum ReferenceAccessKind {
    Read,
    Write,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ReferenceAccessSourceId {
    pub(crate) import_identity: Arc<str>,
    pub(crate) function: Arc<str>,
    pub(crate) block: usize,
    pub(crate) statement: usize,
    pub(crate) node: usize,
    pub(crate) reference_local: Arc<str>,
    pub(crate) kind: ReferenceAccessKind,
}

/// Store observations compare neutrally and never authorize a store or end.
/// Checked borrow endings are explicit statements with semantic identity.
#[derive(Clone, Debug, Default)]
pub struct StatementStoreSource(Option<Arc<ReferenceAccessSourceId>>);
impl StatementStoreSource {
    pub(crate) fn new(source: ReferenceAccessSourceId) -> Self {
        Self(Some(Arc::new(source)))
    }
    pub(crate) fn as_ref(&self) -> Option<&ReferenceAccessSourceId> {
        self.0.as_deref()
    }
}
impl PartialEq for StatementStoreSource {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for StatementStoreSource {}
impl std::hash::Hash for StatementStoreSource {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl Ord for StatementStoreSource {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for StatementStoreSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// Constructed only from a kernel producer's completed read or checked store.
/// Matching source provenance alone never constructs this observation.
#[derive(Debug)]
pub(crate) struct ExecutedReferenceAccess<'a> {
    source: &'a ReferenceAccessSourceId,
    pointer: &'a Pointer,
}

#[derive(Debug)]
pub(crate) enum ExecutedReferenceBoundary<'a> {
    Borrow {
        source: &'a ReferenceBorrowSourceId,
        pointer: &'a Pointer,
    },
    Store(ExecutedReferenceAccess<'a>),
}

/// One optional provenance slot for completed reads and reference births.
/// Payloads are shared and allocated only for observed producers; comparison
/// ignores metadata. Pure facts do not pay for an extra slot for each kind.
#[derive(Clone, Debug, Default)]
pub(crate) struct ReferenceObservationSource(Option<Arc<ReferenceObservation>>);
#[derive(Debug)]
enum ReferenceObservation {
    Read {
        source: Arc<ReferenceAccessSourceId>,
        pointer: Pointer,
        retained_state: MemoryStateIdentity,
        value_type: ProgramType,
    },
    Borrow(ReferenceBorrowObservation),
}
impl ReferenceObservationSource {
    pub(super) fn new(
        source: Arc<ReferenceAccessSourceId>,
        pointer: Pointer,
        memory: &Memory,
        value_type: ProgramType,
    ) -> Self {
        Self(Some(Arc::new(ReferenceObservation::Read {
            source,
            pointer,
            retained_state: MemoryStateIdentity::of(memory),
            value_type,
        })))
    }
    pub(super) fn is_some(&self) -> bool {
        self.0.is_some()
    }
    #[cfg(test)]
    fn is_borrow(&self) -> bool {
        matches!(self.0.as_deref(), Some(ReferenceObservation::Borrow(_)))
    }
    pub(super) fn matches_proposition(&self, proposition: &Proposition) -> bool {
        self.0.as_deref().is_none_or(|observation| match observation {
            ReferenceObservation::Read { source: _, pointer: expected, retained_state, value_type: expected_type } => matches!(proposition,
                Proposition::MemoryReadDefined { memory, pointer, value_type }
                if *retained_state == MemoryStateIdentity::of(memory) && expected == pointer && expected_type == value_type),
            ReferenceObservation::Borrow(birth) => matches!(proposition,
                Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true)
                if left.as_ref() == &birth.pointer && right.as_ref() == &birth.pointer),
        })
    }
}
impl PartialEq for ReferenceObservationSource {
    fn eq(&self, _: &Self) -> bool {
        true
    }
}
impl Eq for ReferenceObservationSource {}
impl std::hash::Hash for ReferenceObservationSource {
    fn hash<H: std::hash::Hasher>(&self, _: &mut H) {}
}
impl Ord for ReferenceObservationSource {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl PartialOrd for ReferenceObservationSource {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl ExecutedReferenceAccess<'_> {
    pub(crate) fn source(&self) -> &ReferenceAccessSourceId {
        self.source
    }
    pub(crate) fn pointer(&self) -> &Pointer {
        self.pointer
    }
}

impl SymbolicExecution {
    /// Selected producer order, grouped by the execution path that actually
    /// completed each operation. A label alone cannot construct a boundary.
    pub(crate) fn executed_reference_boundaries(
        &self,
    ) -> impl Iterator<Item = (usize, ExecutedReferenceBoundary<'_>)> {
        self.paths
            .iter()
            .enumerate()
            .flat_map(|(path_index, path)| {
                path.effect_facts
                    .iter()
                    .chain(path.facts.iter())
                    .filter_map(move |fact| {
                        if !fact.certified {
                            return None;
                        }
                        if let Some(ReferenceObservation::Borrow(birth)) =
                            fact.reference_observation.0.as_deref()
                        {
                            return Some((
                                path_index,
                                ExecutedReferenceBoundary::Borrow {
                                    source: &birth.source,
                                    pointer: &birth.pointer,
                                },
                            ));
                        }
                        let store = fact.certified_store.as_ref()?;
                        let source = store.source.as_ref()?;
                        (source.kind == ReferenceAccessKind::Write).then_some((
                            path_index,
                            ExecutedReferenceBoundary::Store(ExecutedReferenceAccess {
                                source,
                                pointer: &store.pointer,
                            }),
                        ))
                    })
            })
    }
    /// Walk this selected execution's actual effects, without consulting
    /// ambient proof facts or scanning an environment/history.
    pub(crate) fn executed_reference_accesses(
        &self,
    ) -> impl Iterator<Item = ExecutedReferenceAccess<'_>> {
        self.paths
            .iter()
            .flat_map(|path| path.effect_facts.iter().chain(path.facts.iter()))
            .flat_map(|fact| {
                let store = fact.certified_store.as_ref().and_then(|store| {
                    let source = store.source.as_ref()?;
                    (fact.certified && source.kind == ReferenceAccessKind::Write).then_some(
                        ExecutedReferenceAccess {
                            source,
                            pointer: &store.pointer,
                        },
                    )
                });
                let read = fact
                    .reference_observation
                    .0
                    .as_deref()
                    .and_then(|observation| {
                        let ReferenceObservation::Read {
                            source, pointer, ..
                        } = observation
                        else {
                            return None;
                        };
                        (fact.certified && source.kind == ReferenceAccessKind::Read)
                            .then_some(ExecutedReferenceAccess { source, pointer })
                    });
                store.into_iter().chain(read)
            })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn borrow_fact() -> ExecutionPureFact {
        let pointer = Pointer {
            block: "birth".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = ExecutionState::new().with_local(
            "parent",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
        let after = before.clone().with_local(
            "child",
            ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer),
        );
        StatementAssignSource::new(ReferenceBorrowSourceId {
            import_identity: "locked".into(),
            function: "borrow".into(),
            block: 0,
            statement: 0,
            parent: "parent".into(),
            child: "child".into(),
        })
        .completed(&before, &after, "child")
        .unwrap()
    }
    #[test]
    fn source_reference_rewritten_birth_discards_its_observation() {
        let fact = borrow_fact();
        assert!(
            fact.clone()
                .with_proposition(fact.proposition().clone())
                .reference_observation
                .is_borrow()
        );
        assert!(
            !fact
                .with_proposition(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::constant(0)),
                        right: Box::new(MachineTerm::constant(0))
                    },
                    true
                ))
                .reference_observation
                .is_borrow()
        );
    }
    #[test]
    fn source_reference_birth_requires_the_completed_parent_pointer_and_type() {
        let pointer = Pointer {
            block: "birth".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = ExecutionState::new().with_local(
            "parent",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
        let source = StatementAssignSource::new(ReferenceBorrowSourceId {
            import_identity: "locked".into(),
            function: "borrow".into(),
            block: 0,
            statement: 0,
            parent: "parent".into(),
            child: "child".into(),
        });
        let different_pointer = before.clone().with_local(
            "child",
            ProgramValue::typed_pointer(pointer.offset_by_bytes(4), ProgramType::Int32Pointer),
        );
        assert!(
            source
                .completed(&before, &different_pointer, "child")
                .is_none()
        );
        let different_type = before.clone().with_local(
            "child",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer),
        );
        assert!(
            source
                .completed(&before, &different_type, "child")
                .is_none()
        );
        let after = before.clone().with_local(
            "child",
            ProgramValue::typed_pointer(pointer, ProgramType::Int32Pointer),
        );
        assert!(source.completed(&before, &after, "other").is_none());
        assert!(
            source
                .completed(&ExecutionState::new(), &after, "child")
                .is_none()
        );
    }
    fn read_fact() -> ExecutionPureFact {
        let pointer = Pointer {
            block: "source-read".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = Memory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), int32(7));
        let source = Arc::new(ReferenceAccessSourceId {
            import_identity: "locked".into(),
            function: "read".into(),
            block: 0,
            statement: 1,
            node: 0,
            reference_local: "child".into(),
            kind: ReferenceAccessKind::Read,
        });
        let mut fact = ExecutionPureFact::certified(Proposition::MemoryReadDefined {
            memory: memory.clone(),
            pointer: pointer.clone(),
            value_type: ProgramType::Int32,
        });
        fact.public = false;
        fact.logical_read_equation = true;
        fact.reference_observation =
            ReferenceObservationSource::new(source, pointer, &memory, ProgramType::Int32);
        fact
    }
    #[test]
    fn source_reference_rewritten_fact_discards_its_read_observation() {
        let fact = read_fact();
        let unchanged = fact.clone().with_proposition(fact.proposition().clone());
        assert!(unchanged.reference_observation.is_some());
        let mut changed = fact.proposition().clone();
        let Proposition::MemoryReadDefined { pointer, .. } = &mut changed else {
            panic!()
        };
        *pointer = pointer.offset_by_bytes(4);
        assert!(
            !fact
                .with_proposition(changed)
                .reference_observation
                .is_some()
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/source_access/tests.rs");
    }
}
