//! Exact, persistent admission inputs owned by the equality service.
//! These indexes retain source spellings and premises for certificate
//! selection. They are not independent equality decisions.
use crate::kernel::primitives::*;

#[derive(Clone, Debug, Default)]
pub(in crate::kernel) struct InputData {
    pub(in crate::kernel) wide_constant_sources: super::wide_sources::WideEqualitySources,
    /// Value-level pointer origins. C address comparisons never enter this graph.
    pub(in crate::kernel) pointer_address_sources: crate::persistent::PersistentMap<
        ConditionTerm,
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    pub(in crate::kernel) designation_graph:
        crate::kernel::pointer_designations::ValueClasses<Pointer>,
    pub(in crate::kernel) extent_graph: crate::kernel::pointer_designations::ValueClasses<Pointer>,
    pub(in crate::kernel) pointer_value_classes:
        crate::kernel::pointer_designations::ValueClasses<PointerValue>,
    pub(in crate::kernel) pointer_value_equalities:
        crate::persistent::PersistentSet<(PointerValue, PointerValue)>,

    /// Conservative source-dependency selectors for parameter-store shortcuts.
    /// These record syntax, not equality classes or permission authority.
    pub(in crate::kernel) scalar_dependencies: crate::persistent::PersistentSet<Variable>,
    /// Whether an admitted scalar input has a deferred (state) dependency.
    pub(in crate::kernel) scalar_deferred_inputs: bool,
    /// Canonical edge receipts retain admission-time spellings.
    pub(in crate::kernel) uint64_input_edges:
        crate::persistent::PersistentMap<ConditionTerm, (super::MachineAtom, super::MachineAtom)>,
    /// Full-width load premises by exact address and interpretation. MemoryState
    /// transport checks only this bucket; it never scans ambient conditions.
    pub(in crate::kernel) wide_load_sources: crate::persistent::PersistentMap<
        (Pointer, LoadKind),
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    /// True 64-bit equalities as an undirected adjacency map, derived
    /// incrementally from `condition_facts`. Unchanged branches share it;
    /// inserting an equality updates only its two endpoints.
    pub(in crate::kernel) bitvector64_equality_facts: crate::persistent::PersistentMap<
        crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey,
        crate::persistent::PersistentMap<MachineTerm, ConditionTerm>,
    >,
    /// Exact literal-pinning source premises, in deterministic source order.
    pub(in crate::kernel) exact_constant_equalities: crate::persistent::PersistentMap<
        crate::kernel::assumptions::checked_scalar_facts::ScalarOperandKey,
        crate::persistent::PersistentMap<ConditionTerm, i64>,
    >,
    /// Exact alignment premises, including their numeric address annotations.
    pub(in crate::kernel) pointer_alignment_facts: crate::persistent::PersistentMap<
        (Pointer, u64),
        crate::persistent::PersistentSet<ConditionTerm>,
    >,
    /// Exact equalities between two pointers of *different* blocks, indexed
    /// under each side and carrying the fact that states them. An equality
    /// inside one block is a `PointerOffsetEqual` that never reaches this
    /// index (`ConditionTerm::pointer_equal`), so an entry here always says
    /// that two block spellings name one address. Derived incrementally from
    /// `condition_facts`, like every other index above, so asking what one
    /// pointer is proved equal to is a keyed lookup rather than a scan of
    /// every pointer comparison the path happens to hold.
    pub(in crate::kernel) pointer_block_aliases: crate::persistent::PersistentMap<
        Pointer,
        crate::persistent::PersistentMap<Pointer, ConditionTerm>,
    >,
    /// Cross-block alias endpoints grouped by object. External arguments
    /// use their offset stem, since all parameters share one block; other
    /// blocks use one bucket. Derived incrementally from exact aliases.
    pub(in crate::kernel) pointer_alias_endpoints_by_object:
        crate::persistent::PersistentMap<Pointer, crate::persistent::PersistentSet<Pointer>>,
    /// Pointer-address endpoints of full-width equalities, by object.
    /// Lets store framing follow address copies without scanning size facts.
    pub(in crate::kernel) wide_pointer_alias_endpoints_by_object:
        crate::persistent::PersistentMap<Pointer, crate::persistent::PersistentSet<MachineTerm>>,
    pub(in crate::kernel) algebraic_graph_equalities: crate::persistent::PersistentMap<
        (
            crate::kernel::SharedPureApplication,
            crate::kernel::SharedPureApplication,
        ),
        (),
    >,
    pub(in crate::kernel) congruence_conditions:
        crate::persistent::PersistentMap<ConditionTerm, bool>,
    /// Exact defining equations for pointer-typed reads issued on this path,
    /// indexed by their load variable. Producer metadata certifies the C
    /// value's type; the equation supplies its state and address. Both
    /// are required before a graph query may use the read as a bridge.
    pub(in crate::kernel) typed_pointer_read_definitions: crate::persistent::PersistentMap<
        Variable,
        crate::persistent::PersistentMap<((u32, u32), Pointer), (Pointer, SharedMemory)>,
    >,
    pub(in crate::kernel) uint64_graph_equalities: crate::persistent::PersistentMap<
        (
            crate::kernel::equality_graph::MachineAtom,
            crate::kernel::equality_graph::MachineAtom,
        ),
        (),
    >,
    /// The canonical oriented edges of exact int32 premises. Several
    /// spellings can name one edge.
    pub(in crate::kernel) int32_graph_equalities: crate::persistent::PersistentMap<
        (
            crate::kernel::equality_graph::MachineAtom,
            crate::kernel::equality_graph::MachineAtom,
        ),
        (),
    >,
    /// Normalized same-block pointer equalities, indexed under each offset.
    pub(in crate::kernel) pointer_offset_aliases: crate::persistent::PersistentMap<
        PointerOffsetTerm,
        crate::persistent::PersistentSet<PointerOffsetTerm>,
    >,
    /// `pointer_offset_aliases` again, keyed by the alias offset's root atom
    /// (`resource_algebra::offset_root_atom`).
    pub(in crate::kernel) pointer_offset_aliases_by_root: crate::persistent::PersistentMap<
        Option<PointerOffsetTerm>,
        crate::persistent::PersistentSet<(PointerOffsetTerm, PointerOffsetTerm)>,
    >,
    /// Admission-time keys of the admitted scalar evidence inputs.
    pub(in crate::kernel) scalar_evidence_keys: crate::persistent::PersistentMap<
        ConditionTerm,
        (SharedMachineIntegerTerm, SharedMachineIntegerTerm),
    >,
    /// Direct written scalar-to-literal equalities, independent of native vs
    /// shared comparison spelling.
    pub(in crate::kernel) scalar_literal_inputs:
        crate::persistent::PersistentSet<(SharedMachineIntegerTerm, u32)>,
    /// Canonical source endpoints and their exact admitted premises. Used only
    /// for evidence enumeration and paths, never as a second equality decision.
    pub(in crate::kernel) scalar_evidence_inputs: crate::persistent::PersistentMap<
        SharedMachineIntegerTerm,
        crate::persistent::PersistentMap<
            SharedMachineIntegerTerm,
            crate::persistent::PersistentMap<ConditionTerm, Proposition>,
        >,
    >,
    /// Exact equalities between two applications of one algebraic
    /// constructor, indexed by each field equality they entail. Both levels
    /// are persistent so adding one proof fact changes logarithmically many
    /// nodes instead of cloning an ambient fact table.
    pub(in crate::kernel) algebraic_constructor_field_equalities: crate::persistent::PersistentMap<
        Proposition,
        crate::persistent::PersistentMap<(Proposition, usize), ()>,
    >,
}

/// Source premises may themselves carry memory/proof contexts. Erasing only
/// this owning allocation breaks the recursive Send/Sync type path through
/// resource indexes that retain a graph. Access stays typed inside the service;
/// clones share this allocation until their first source mutation.
#[derive(Clone)]
pub(in crate::kernel) struct AdmittedInputs(std::sync::Arc<dyn std::any::Any + Send + Sync>);

impl Default for AdmittedInputs {
    fn default() -> Self {
        Self(std::sync::Arc::new(InputData::default()))
    }
}
impl std::fmt::Debug for AdmittedInputs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AdmittedInputs").finish_non_exhaustive()
    }
}
impl std::ops::Deref for AdmittedInputs {
    type Target = InputData;
    fn deref(&self) -> &InputData {
        self.0
            .downcast_ref()
            .expect("equality service input allocation")
    }
}
impl std::ops::DerefMut for AdmittedInputs {
    fn deref_mut(&mut self) -> &mut InputData {
        if std::sync::Arc::get_mut(&mut self.0).is_none() {
            self.0 = std::sync::Arc::new((**self).clone());
        }
        std::sync::Arc::get_mut(&mut self.0)
            .expect("unique input allocation")
            .downcast_mut()
            .expect("equality service input allocation")
    }
}
