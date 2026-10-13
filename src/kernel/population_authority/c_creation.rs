//! Provenance of C storage created by the executing proof environment.
//!
//! This optional event ledger binds abstract population authority to checked
//! C storage creation. It grants no C memory permission, and assumed
//! allocation claims never enter it.

use super::{Anchor, AuthorityState, Holder, Refusal};
use crate::kernel::{
    AlgebraicValue, Bitvector32Term, CCompositeResourceDefinition, CResource, CResourceFact,
    CState, CValue, PointerBlock, PointerOffsetTerm, PureFactContext, ResourceDescription,
    ResourceReference,
};
use crate::persistent::{PersistentMap, PersistentSet};
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

fn fresh_identity() -> u64 {
    static NEXT: AtomicU64 = AtomicU64::new(1);
    NEXT.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("C population creation identity exhausted")
}

fn same_quantity(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || crate::kernel::quantity_condition_holds(
            assumptions,
            crate::kernel::ConditionTerm::Bitvector32Equal(
                Box::new(left.clone()),
                Box::new(right.clone()),
            ),
        )
}

/// Resolve a numerical request from its literal or exact recorded value, or
/// an equality with the sender's complete batch. The caller checks custody;
/// neither a global count nor a bound can supply missing member rights.
fn numerical_batch_quantity(
    quantity: &Bitvector32Term,
    held: u32,
    assumptions: &PureFactContext,
) -> Option<u32> {
    quantity
        .as_const()
        .or_else(|| {
            crate::kernel::assumptions::exact_signed_constant(quantity, assumptions)
                .filter(|value| (0..=i64::from(i32::MAX)).contains(value))
                .map(|value| value as u32)
        })
        .or_else(|| {
            (assumptions.exact_condition_value(&crate::kernel::ConditionTerm::equal(
                quantity.clone(),
                Bitvector32Term::Constant(held),
            )) == Some(true))
            .then_some(held)
        })
}

/// Quantities and named occurrences use the same conservation ledger, but
/// only a checked named-instance rewrite can manipulate a field-bearing member.
#[derive(Clone, Copy)]
enum MemberForm {
    Quantity { exclusive_body: bool },
    Instance,
}

/// Named custody remains exclusively in the checked resource context. A
/// named authority import supplies an arbitrary population total, never
/// anonymous member rights. Checked named consumption records exact identities.
enum OpaqueMemberInputs {
    Quantity(Option<ResourceDescription>),
    NamedAuthority,
    /// A typed lock in a standalone body. Its anchor is the caller's pointer,
    /// which no storage created earlier in this proof can alias.
    Acquired,
}

struct Root {
    identity: u64,
    /// Stable rechecking of the same function-entry transition. C calls remain
    /// closed until each occurrence has its own identity.
    entry_call: OnceLock<CreationEvents>,
    proof_entry: OnceLock<CreationEvents>,
    /// Rechecking a transfer or return uses the same successor identity.
    /// Keys contain only small holder/population IDs, never resource trees.
    transfers:
        Mutex<BTreeMap<(Holder, Holder, super::Population, bool, Bitvector32Term), CreationEvents>>,
    returns: Mutex<BTreeMap<u64, CreationEvents>>,
    c_events: Mutex<BTreeMap<CEvent, CreationEvents>>,
    invocation: Holder,
    /// Standalone proof entry preserves only declared opaque custody; the C
    /// invocation remains fresh and cannot inherit storage creation rights.
    opaque_actor: Holder,
    pending: PersistentMap<PointerBlock, Holder>,
    creators: PersistentMap<PointerBlock, Holder>,
    anchors: PersistentMap<PointerBlock, Anchor>,
    authority: AuthorityState,
    scopes: PersistentMap<(PointerBlock, String), ResourceDescription>,
    /// Exact identities in concrete wildcard populations; totals remain in AuthorityState.
    exact_members: PersistentMap<ResourceDescription, u32>,
    opaque_types: PersistentMap<ResourceDescription, ResourceDescription>,
    /// One symbolic member batch per live population, with its owning holder.
    symbolic_batches: PersistentMap<super::Population, SymbolicBatch>,
    symbolic_holders: PersistentMap<Holder, u32>,
    /// Per-storage family history; never inferred from the current owner.
    tainted: PersistentMap<PointerBlock, PersistentSet<String>>,
    /// Exact declared population inputs. Each carries no creator right,
    /// storage event, or asserted total.
    opaque_imports: PersistentMap<ResourceDescription, OpaqueImport>,
    /// Number of authority/member fragments held by each opaque actor.
    /// Call completion checks this index without visiting unrelated imports.
    opaque_holders: PersistentMap<Holder, u32>,
    opaque_transfers:
        Mutex<BTreeMap<(Holder, Holder, u64, ResourceDescription, bool, u32), CreationEvents>>,
    opaque_entry_counts: Mutex<BTreeMap<ResourceDescription, Bitvector32Term>>,
    empty_populations: PersistentMap<PointerBlock, PersistentSet<String>>,
}

#[derive(Clone)]
struct SymbolicBatch {
    owner: Holder,
    quantity: Bitvector32Term,
}

#[derive(Clone)]
struct OpaqueImport {
    identity: u64,
    authority_holder: Holder,
    member_holders: PersistentMap<Holder, u32>,
    description: ResourceDescription,
    /// A wildcard helper borrows one identified member, not an arbitrary unit.
    wildcard_member: Option<ResourceDescription>,
    /// Exclusively owned private bodies give each exact member a unique unit.
    /// Ownership is keyed independently of the aggregate population total.
    private_members: PersistentMap<ResourceDescription, PrivateMember>,
    private_birth_generation: u64,
    /// Stable arbitrary exact counts shared by all successors of this import.
    exact_entry_counts: Arc<Mutex<BTreeMap<ResourceDescription, Bitvector32Term>>>,
    /// The checked definition used to open this exact entry control for a
    /// read-only count observation. Current ownership is checked on each read.
    control: Option<(CResourceFact, Arc<CCompositeResourceDefinition>)>,
    entry_owned_members: u32,
    owned_members: u32,
    /// Symbolic cardinality is admitted only through a checked control wrapper.
    entry_symbolic_members: Option<Bitvector32Term>,
    /// Whole-batch custody is independent of the authority holder.
    symbolic_member_holder: Option<Holder>,
    symbolic_delta: Option<(bool, Bitvector32Term)>,
    /// Occurrences consumed by checked named rewrites, independent of count observations.
    consumed_named: PersistentMap<crate::kernel::Variable, Arc<crate::kernel::ResourceInstance>>,
    /// Named births remain distinct from entry occurrences, even after death.
    born_named: PersistentMap<crate::kernel::Variable, ()>,
    named_counts: PersistentMap<ResourceDescription, NamedCountChange>,
    /// Unresolved indices permit exact observation only of this single selection.
    named_selection: Option<ResourceDescription>,
    named_ambiguous: bool,
    /// Only a checked control wrapper can supply this immutable entry load.
    entry_count: Option<Bitvector32Term>,
    retired_authority: bool,
}

#[derive(Clone, Default)]
struct NamedCountChange {
    delta: i32,
    entry_deaths: u32,
}

#[derive(Clone)]
struct PrivateMember {
    owner: Option<Holder>,
    /// A later birth at an unresolved alias invalidates a remembered absence.
    zero_generation: u64,
}

pub(in crate::kernel) struct SymbolicPopulationCount {
    pub entry_count: Bitvector32Term,
    pub delta: i32,
    pub entry_owned_members: u32,
    pub entry_symbolic_members: Option<Bitvector32Term>,
    pub symbolic_delta: Option<(bool, Bitvector32Term)>,
}

impl SymbolicPopulationCount {
    /// Preserve both components of a checked symbolic birth followed by
    /// numerical births. Other mixed directions are not admitted by the ledger.
    pub(in crate::kernel) fn combined_delta(&self) -> Option<(bool, Bitvector32Term)> {
        match (&self.symbolic_delta, self.delta) {
            (Some((true, quantity)), delta) if delta > 0 => Some((
                true,
                Bitvector32Term::add(quantity.clone(), Bitvector32Term::Constant(delta as u32)),
            )),
            (Some(delta), _) => Some(delta.clone()),
            (None, delta) if delta != 0 => {
                Some((delta > 0, Bitvector32Term::Constant(delta.unsigned_abs())))
            }
            (None, _) => None,
        }
    }
}

impl OpaqueImport {
    fn has_composable_symbolic_birth(&self) -> bool {
        self.entry_symbolic_members.is_none()
            && self.entry_owned_members == 0
            && matches!(self.symbolic_delta, Some((true, _)))
    }
}

/// Inputs of a checked C lifetime event. Each key is proportional to the
/// pointer or family named by that one operation.
#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
enum CEvent {
    Control(CResourceFact),
    Pending(PointerBlock),
    Resolve(PointerBlock, Option<PointerBlock>),
    Created(PointerBlock),
    MemberCreated(PointerBlock, String),
    Retired(PointerBlock),
    InstanceMember(ResourceReference, bool),
    TransferredAnchor(Holder, Holder, PointerBlock),
    AcquiredControl(ResourceDescription, u32),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::kernel) enum CreationRefusal {
    NotCreationEnvironment,
    MembersAlreadyExisted,
    AlreadyEstablished,
    MissingAuthority,
    MissingMembers,
    InvalidMember,
    InvalidQuantity,
    PopulationCountOverflow,
    OutstandingMembers,
    OutstandingAuthority,
    OutstandingOwnership,
    UnknownTotal,
    OpaqueImportConflict,
}

impl From<Refusal> for CreationRefusal {
    fn from(value: Refusal) -> Self {
        match value {
            Refusal::AlreadyEstablished => Self::AlreadyEstablished,
            Refusal::OutstandingMembers => Self::OutstandingMembers,
            Refusal::OutstandingAuthority => Self::OutstandingAuthority,
            Refusal::MissingAuthority | Refusal::UnknownPopulation => Self::MissingAuthority,
            Refusal::MissingMembers => Self::MissingMembers,
            Refusal::InvalidQuantity => Self::InvalidQuantity,
            Refusal::OutstandingOwnership => Self::OutstandingOwnership,
            _ => Self::NotCreationEnvironment,
        }
    }
}

/// Opaque evidence issued only by a checked transition that minted the
/// resulting abstract population identity. Certificate checking compares exact state roots;
/// it never tries to allocate the same identity a second time.
#[derive(Clone, Debug)]
pub(crate) struct CheckedPopulationAuthorityExchange {
    before: u64,
    after: u64,
    description: ResourceDescription,
    establish: bool,
}

/// Evidence for one member entering or leaving a registered population.
/// The proof checker must also check the corresponding resource exchange.
#[derive(Clone, Debug)]
pub(crate) struct CheckedPopulationMemberExchange {
    before: u64,
    after: u64,
    description: ResourceDescription,
    produce: bool,
}

impl CheckedPopulationMemberExchange {
    pub(in crate::kernel) fn matches(
        &self,
        before: &CreationEvents,
        after: &CreationEvents,
        description: &ResourceDescription,
        produce: bool,
    ) -> bool {
        self.before == before.0.identity
            && self.after == after.0.identity
            && &self.description == description
            && self.produce == produce
    }
}

impl CheckedPopulationAuthorityExchange {
    pub(in crate::kernel) fn matches(
        &self,
        before: &CreationEvents,
        after: &CreationEvents,
        description: &ResourceDescription,
        establish: bool,
    ) -> bool {
        self.before == before.0.identity
            && self.after == after.0.identity
            && &self.description == description
            && self.establish == establish
    }
}

/// Exact storage-block creation evidence. Copies of a proof path share a root;
/// each transition makes one new root, so state comparison never scans events.
#[derive(Clone)]
pub(in crate::kernel) struct CreationEvents(Arc<Root>);

impl std::fmt::Debug for CreationEvents {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CreationEvents")
            .field("identity", &self.0.identity)
            .field("invocation", &self.0.invocation)
            .field("pending_count", &self.0.pending.len())
            .field("event_count", &self.0.creators.len())
            .field("anchor_count", &self.0.anchors.len())
            .field("tainted_blocks", &self.0.tainted.len())
            .finish()
    }
}

impl PartialEq for CreationEvents {
    fn eq(&self, other: &Self) -> bool {
        self.0.identity == other.0.identity
    }
}
impl Eq for CreationEvents {}
impl PartialOrd for CreationEvents {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for CreationEvents {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.identity.cmp(&other.0.identity)
    }
}
impl Hash for CreationEvents {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.identity.hash(state);
    }
}

impl CreationEvents {
    /// Whether this ledger records nothing: no storage, member, authority,
    /// import, scope or batch. Its identity and holders are fresh names that
    /// nothing else in its state can refer to, so two such ledgers describe
    /// the same population state.
    pub(in crate::kernel) fn records_nothing(&self) -> bool {
        let root = &self.0;
        root.pending.is_empty()
            && root.creators.is_empty()
            && root.anchors.is_empty()
            && root.authority.is_empty()
            && root.scopes.is_empty()
            && root.exact_members.is_empty()
            && root.opaque_types.is_empty()
            && root.symbolic_batches.is_empty()
            && root.symbolic_holders.is_empty()
            && root.tainted.is_empty()
            && root.opaque_imports.is_empty()
            && root.opaque_holders.is_empty()
            && root.empty_populations.is_empty()
    }

    /// Whether two ledgers record the same storage, member, authority and
    /// scope state. Each transition mints a fresh identity, so two paths
    /// whose transitions net out the same, such as one that created and
    /// retired a local and one that never declared it, hold equal records
    /// under different identities. Records that carry identities of their
    /// own, opaque imports and symbolic batches, must be the very same
    /// records. Comparing two separately built maps visits their entries.
    pub(in crate::kernel) fn records_same_state_as(&self, other: &Self) -> bool {
        let (left, right) = (&self.0, &other.0);
        left.identity == right.identity
            || left.anchors == right.anchors
                && left.authority == right.authority
                && Self::same_records_besides_anchors(left, right)
    }

    /// Whether two ledgers differ only in the fresh anchors their paths gave
    /// the same storage. Two arms of a branch that each declare the same
    /// local after their ledgers diverged each mint an anchor for it. An
    /// anchor with no population established on it is named nowhere else, so
    /// the two ledgers record the same state. This visits the anchor maps.
    pub(in crate::kernel) fn records_same_state_up_to_fresh_anchors(&self, other: &Self) -> bool {
        let (left, right) = (&self.0, &other.0);
        if left.anchors.len() != right.anchors.len() {
            return false;
        }
        let mut renamed = Vec::new();
        for (block, anchor) in left.anchors.iter() {
            match right.anchors.get(block) {
                Some(other_anchor) if other_anchor == anchor => {}
                Some(other_anchor) => renamed.push((*anchor, *other_anchor)),
                None => return false,
            }
        }
        !renamed.is_empty()
            && left
                .authority
                .same_up_to_unestablished_anchors(&right.authority, &renamed)
            && Self::same_records_besides_anchors(left, right)
    }

    fn same_records_besides_anchors(left: &Root, right: &Root) -> bool {
        left.invocation == right.invocation
            && left.opaque_actor == right.opaque_actor
            && left.pending == right.pending
            && left.creators == right.creators
            && left.scopes == right.scopes
            && left.exact_members == right.exact_members
            && left.opaque_types == right.opaque_types
            && left
                .symbolic_batches
                .shares_root_with(&right.symbolic_batches)
            && left.symbolic_holders == right.symbolic_holders
            && left.tainted == right.tainted
            && left.opaque_imports.shares_root_with(&right.opaque_imports)
            && left.opaque_holders == right.opaque_holders
            && left.empty_populations == right.empty_populations
    }

    fn memoized_c_event(&self, key: CEvent, create: impl FnOnce() -> Self) -> Self {
        if let Some(existing) = self.0.c_events.lock().expect("C event cache").get(&key) {
            return existing.clone();
        }
        let next = create();
        self.0
            .c_events
            .lock()
            .expect("C event cache")
            .entry(key)
            .or_insert(next)
            .clone()
    }

    /// A typed mutex acquisition in a standalone proof enters one population
    /// with an arbitrary total. Rechecking the same acquisition from the same
    /// ledger reuses its import, so independent rechecks agree on its identity.
    pub(in crate::kernel) fn import_acquired_control_population(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
    ) -> Result<Self, CreationRefusal> {
        let key = CEvent::AcquiredControl(description.clone(), owned_members);
        if let Some(existing) = self.0.c_events.lock().expect("C event cache").get(&key) {
            return Ok(existing.clone());
        }
        let next = self.import_opaque_contract_population_with_member(
            description,
            owned_members,
            Some(self.fresh_opaque_entry_count(description)?),
            None,
            None,
            OpaqueMemberInputs::Acquired,
        )?;
        Ok(self.memoized_c_event(key, || next))
    }

    #[cfg(test)]
    /// Standalone helper entry may assume one already existing population
    /// named by an exact external-argument pointer. This records only the
    /// contract's input custody; it cannot create storage or assert a total.
    pub(in crate::kernel) fn import_opaque_contract_population(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
    ) -> Result<Self, CreationRefusal> {
        self.import_opaque_contract_population_inner(description, owned_members, None, None, None)
    }

    /// A direct unary authority permits observation of an arbitrary existing
    /// total, just like a wildcard authority. Custody never asserts that total.
    pub(in crate::kernel) fn import_observable_contract_population(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
    ) -> Result<Self, CreationRefusal> {
        self.import_observable_contract_population_quantity(
            description,
            &Bitvector32Term::Constant(owned_members),
        )
    }

    /// The arbitrary entry total of an opaque import, stable across rechecks
    /// of the same ledger.
    fn fresh_opaque_entry_count(
        &self,
        description: &ResourceDescription,
    ) -> Result<Bitvector32Term, CreationRefusal> {
        if let Some(import) = self.0.opaque_imports.get(description) {
            return import
                .entry_count
                .clone()
                .ok_or(CreationRefusal::UnknownTotal);
        }
        Ok(self
            .0
            .opaque_entry_counts
            .lock()
            .expect("opaque entry count cache")
            .entry(description.clone())
            .or_insert_with(|| {
                Bitvector32Term::Variable(
                    crate::kernel::Variable::allocate_fresh()
                        .expect("opaque count identity exhausted"),
                )
            })
            .clone())
    }

    pub(in crate::kernel) fn import_observable_contract_population_quantity(
        &self,
        description: &ResourceDescription,
        quantity: &Bitvector32Term,
    ) -> Result<Self, CreationRefusal> {
        let (owned_members, symbolic_members) = match quantity.as_const() {
            Some(value) if value <= i32::MAX as u32 => (value, None),
            Some(_) => return Err(CreationRefusal::InvalidQuantity),
            None => (0, Some(quantity.clone())),
        };
        let count = self.fresh_opaque_entry_count(description)?;
        self.import_opaque_contract_population_inner(
            description,
            owned_members,
            Some(count),
            symbolic_members,
            None,
        )
    }

    pub(in crate::kernel) fn import_observable_named_authority(
        &self,
        description: &ResourceDescription,
    ) -> Result<Self, CreationRefusal> {
        if description.schema().is_fieldless() {
            return Err(CreationRefusal::InvalidMember);
        }
        let count = if let Some(import) = self.0.opaque_imports.get(description) {
            import
                .entry_count
                .clone()
                .ok_or(CreationRefusal::UnknownTotal)?
        } else {
            self.0
                .opaque_entry_counts
                .lock()
                .expect("opaque entry count cache")
                .entry(description.clone())
                .or_insert_with(|| {
                    Bitvector32Term::Variable(
                        crate::kernel::Variable::allocate_fresh()
                            .expect("opaque count identity exhausted"),
                    )
                })
                .clone()
        };
        self.import_opaque_contract_population_with_member(
            description,
            0,
            Some(count),
            None,
            None,
            OpaqueMemberInputs::NamedAuthority,
        )
    }

    /// Borrow an existing wildcard population and one concrete member. Its
    /// total is opaque and may include ownership retained by other callers.
    pub(in crate::kernel) fn import_opaque_wildcard_population(
        &self,
        description: &ResourceDescription,
        member: &ResourceDescription,
    ) -> Result<Self, CreationRefusal> {
        if description.population_arity() != Some(member.arguments().len())
            || member.population_arity().is_some()
            || member.family() != description.family()
            || member.arguments().first() != description.arguments().first()
            || member.schema() != description.schema()
            || !member.resource_arguments().is_empty()
        {
            return Err(CreationRefusal::InvalidMember);
        }
        self.import_opaque_wildcard_input(description, Some(member.clone()))
    }

    pub(in crate::kernel) fn import_opaque_wildcard_authority(
        &self,
        description: &ResourceDescription,
    ) -> Result<Self, CreationRefusal> {
        if description.population_arity().is_none() {
            return Err(CreationRefusal::InvalidMember);
        }
        self.import_opaque_wildcard_input(description, None)
    }

    fn import_opaque_wildcard_input(
        &self,
        description: &ResourceDescription,
        member: Option<ResourceDescription>,
    ) -> Result<Self, CreationRefusal> {
        let count = if let Some(import) = self.0.opaque_imports.get(description) {
            import
                .entry_count
                .clone()
                .ok_or(CreationRefusal::UnknownTotal)?
        } else {
            let mut counts = self
                .0
                .opaque_entry_counts
                .lock()
                .expect("opaque entry count cache");
            counts
                .entry(description.clone())
                .or_insert_with(|| {
                    Bitvector32Term::Variable(
                        crate::kernel::Variable::allocate_fresh()
                            .expect("opaque entry count identity exhausted"),
                    )
                })
                .clone()
        };
        self.import_opaque_contract_population_with_member(
            description,
            u32::from(member.is_some()),
            Some(count),
            None,
            None,
            OpaqueMemberInputs::Quantity(member),
        )
    }

    /// Import only an exact owned wrapper and each contained authority. A
    /// declared counter equality supplies a checked entry load; otherwise a
    /// fresh private symbol names this population's arbitrary entry total.
    #[cfg(test)]
    pub(in crate::kernel) fn import_checked_control_wrapper(
        &self,
        state: &CState,
        selected: &CResourceFact,
        definition: &CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Self, String> {
        self.import_checked_control_wrapper_with_members(
            state,
            selected,
            definition,
            assumptions,
            &BTreeMap::new(),
        )
    }

    pub(in crate::kernel) fn import_checked_control_wrapper_with_members(
        &self,
        state: &CState,
        selected: &CResourceFact,
        definition: &CCompositeResourceDefinition,
        assumptions: &PureFactContext,
        wildcard_members: &BTreeMap<ResourceDescription, Vec<CResourceFact>>,
    ) -> Result<Self, String> {
        if state.population_effects.creation.as_ref() != Some(self) {
            return Err("control import requires the current creation ledger".into());
        }
        let components =
            state.checked_authority_wrapper_import_components(selected, definition, assumptions)?;
        let mut events = self.clone();
        for (description, entry_count) in components {
            let entry_count = match entry_count {
                Some(count) => count,
                None => {
                    if let Some(existing) = events.0.opaque_imports.get(&description) {
                        existing
                            .entry_count
                            .clone()
                            .ok_or("opaque population has no entry count witness")?
                    } else {
                        let mut counts = events
                            .0
                            .opaque_entry_counts
                            .lock()
                            .expect("opaque entry count cache");
                        if let Some(count) = counts.get(&description) {
                            count.clone()
                        } else {
                            let variable = crate::kernel::Variable::allocate_fresh()
                                .ok_or("opaque entry count identity exhausted")?;
                            let count = Bitvector32Term::Variable(variable);
                            counts.insert(description.clone(), count.clone());
                            count
                        }
                    }
                }
            };
            let wildcard_member = if description.population_arity().is_some() {
                match wildcard_members.get(&description).map(Vec::as_slice) {
                    None | Some([]) => None,
                    Some([fact]) => {
                        let CResourceFact::Own(CResource::Composite { name, arguments }, quantity) =
                            fact
                        else {
                            return Err("Requires one owned wildcard member".into());
                        };
                        if quantity.as_const() != Some(1)
                            || name != description.family()
                            || Some(arguments.len()) != description.population_arity()
                            || arguments.first() != description.arguments().first()
                            || !state.resources().contains_exact_representation(fact)
                        {
                            return Err(
                                "Requires the declared concrete member of this authority".into()
                            );
                        }
                        Some(ResourceDescription::new(
                            name.clone(),
                            arguments.clone(),
                            description.schema().clone(),
                        ))
                    }
                    Some(_) => {
                        return Err(
                            "wildcard control entry currently supports one concrete member".into(),
                        );
                    }
                }
            } else {
                None
            };
            let member = CResource::Composite {
                name: description.family().to_owned(),
                arguments: description.arguments().to_vec().into(),
            };
            let owned = state
                .resources()
                .exact_resource_facts(&member)
                .into_iter()
                .filter_map(|fact| fact.owned_quantity_term().cloned())
                .collect::<Vec<_>>();
            let numeric_members = owned
                .iter()
                .try_fold(0_u32, |total, quantity| {
                    total.checked_add(quantity.as_const()?)
                })
                .filter(|n| *n <= i32::MAX as u32);
            let (owned_members, symbolic_members) = if wildcard_member.is_some() {
                (1, None)
            } else {
                match (numeric_members, owned.as_slice()) {
                    (Some(quantity), _) => (quantity, None),
                    (None, [quantity]) => (0, Some(quantity.clone())),
                    _ => return Err("control import needs one owned member quantity".into()),
                }
            };
            events = events
                .import_opaque_contract_population_with_member(
                    &description,
                    owned_members,
                    Some(entry_count),
                    symbolic_members,
                    Some((selected.clone(), Arc::new(definition.clone()))),
                    OpaqueMemberInputs::Quantity(wildcard_member),
                )
                .map_err(|refusal| format!("control import refused: {refusal:?}"))?;
        }
        Ok(events)
    }

    fn import_opaque_contract_population_inner(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
        entry_count: Option<Bitvector32Term>,
        symbolic_members: Option<Bitvector32Term>,
        control: Option<(CResourceFact, Arc<CCompositeResourceDefinition>)>,
    ) -> Result<Self, CreationRefusal> {
        if description.population_arity().is_some() {
            return Err(CreationRefusal::InvalidMember);
        }
        self.import_opaque_contract_population_with_member(
            description,
            owned_members,
            entry_count,
            symbolic_members,
            control,
            OpaqueMemberInputs::Quantity(None),
        )
    }

    fn import_opaque_contract_population_with_member(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
        entry_count: Option<Bitvector32Term>,
        symbolic_members: Option<Bitvector32Term>,
        control: Option<(CResourceFact, Arc<CCompositeResourceDefinition>)>,
        members: OpaqueMemberInputs,
    ) -> Result<Self, CreationRefusal> {
        let named_authority = matches!(members, OpaqueMemberInputs::NamedAuthority);
        let acquired = matches!(members, OpaqueMemberInputs::Acquired);
        if named_authority
            && (description.schema().is_fieldless()
                || owned_members != 0
                || symbolic_members.is_some()
                || control.is_some())
        {
            return Err(CreationRefusal::InvalidMember);
        }
        let wildcard_member = match members {
            OpaqueMemberInputs::Quantity(member) => member,
            OpaqueMemberInputs::NamedAuthority | OpaqueMemberInputs::Acquired => None,
        };
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        if (description.population_arity().is_none() && wildcard_member.is_some())
            || pointer.pointer().block != PointerBlock::ExternalArgument
            || !description.schema().is_fieldless() && !named_authority
            || !description.resource_arguments().is_empty()
            || owned_members > i32::MAX as u32
        {
            return Err(CreationRefusal::InvalidMember);
        }
        if let Some(existing) = self.0.opaque_imports.get(description) {
            if existing.owned_members == owned_members
                && existing.entry_count == entry_count
                && existing.entry_symbolic_members == symbolic_members
                && existing.control == control
                && existing.wildcard_member == wildcard_member
            {
                return Ok(self.clone());
            }
            return Err(CreationRefusal::OpaqueImportConflict);
        }
        if !acquired && (!self.0.creators.is_empty() || !self.0.anchors.is_empty()) {
            return Err(CreationRefusal::NotCreationEnvironment);
        }
        let mut pattern = ResourceDescription::new(
            description.family().into(),
            description.arguments().to_vec().into(),
            crate::kernel::ResourceFieldSchema::new(vec![]).expect("empty schema"),
        );
        if let Some(arity) = description.population_arity() {
            pattern = pattern
                .with_population_arity(arity)
                .map_err(|_| CreationRefusal::InvalidMember)?;
        }
        if named_authority
            && self
                .0
                .opaque_types
                .get(&pattern)
                .is_some_and(|existing| existing != description)
        {
            return Err(CreationRefusal::OpaqueImportConflict);
        }
        let opaque_imports = self.0.opaque_imports.with_inserted(
            description.clone(),
            OpaqueImport {
                identity: fresh_identity(),
                authority_holder: self.0.opaque_actor,
                member_holders: PersistentMap::default()
                    .with_inserted(self.0.opaque_actor, owned_members),
                description: description.clone(),
                wildcard_member,
                private_members: PersistentMap::default(),
                private_birth_generation: 0,
                exact_entry_counts: Arc::new(Mutex::new(BTreeMap::new())),
                control,
                entry_owned_members: owned_members,
                owned_members,
                entry_symbolic_members: symbolic_members.clone(),
                symbolic_member_holder: symbolic_members.as_ref().map(|_| self.0.opaque_actor),
                symbolic_delta: None,
                consumed_named: PersistentMap::default(),
                born_named: PersistentMap::default(),
                named_counts: PersistentMap::default(),
                named_selection: None,
                named_ambiguous: false,
                entry_count,
                retired_authority: false,
            },
        );
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.with_inserted(
                self.0.opaque_actor,
                self.0
                    .opaque_holders
                    .get(&self.0.opaque_actor)
                    .copied()
                    .unwrap_or(0)
                    + 1
                    + u32::from(owned_members > 0 || symbolic_members.is_some()),
            ),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: if named_authority {
                self.0
                    .opaque_types
                    .with_inserted(pattern, description.clone())
            } else {
                self.0.opaque_types.clone()
            },
            opaque_imports,
        })))
    }

    pub(in crate::kernel) fn owns_population_authority(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        if self
            .0
            .opaque_imports
            .get(description)
            .is_some_and(|import| {
                !import.retired_authority && import.authority_holder == self.0.opaque_actor
            })
        {
            return true;
        }
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return false;
        };
        let Ok(block) = self.exact_member_block(&pointer.pointer().block, description) else {
            return false;
        };
        self.0
            .anchors
            .get(block)
            .and_then(|anchor| {
                self.0
                    .authority
                    .population_at(*anchor, description.family())
            })
            .is_some_and(|population| {
                self.0
                    .authority
                    .holder_owns_authority(self.0.invocation, population)
            })
    }

    /// Attach the current checked wrapper to existing imported authorities.
    /// This changes no identity, cardinality, custody, or creation rights.
    pub(in crate::kernel) fn checked_current_control_wrapper(
        &self,
        state: &CState,
        selected: &CResourceFact,
        definition: &CCompositeResourceDefinition,
        assumptions: &PureFactContext,
    ) -> Result<Self, String> {
        if state.population_effects.creation.as_ref() != Some(self) {
            return Err("control registration requires the current creation ledger".into());
        }
        let (children, _) =
            state.checked_authority_wrapper_body(selected, definition, assumptions)?;
        let descriptions = children
            .iter()
            .filter_map(|child| match child.resource() {
                CResource::PopulationAuthority(description) => Some(description.clone()),
                _ => None,
            })
            .collect::<Vec<_>>();
        let mut changed = false;
        for description in &descriptions {
            if let Some(import) = self.0.opaque_imports.get(description) {
                changed |= !import
                    .control
                    .as_ref()
                    .is_some_and(|(fact, body)| fact == selected && body.as_ref() == definition);
            }
        }
        if !changed {
            return Ok(self.clone());
        }
        let next = self.memoized_c_event(CEvent::Control(selected.clone()), || {
            let mut imports = self.0.opaque_imports.clone();
            let body = Arc::new(definition.clone());
            for description in &descriptions {
                if let Some(import) = imports.get(description).cloned() {
                    imports.insert(
                        description.clone(),
                        OpaqueImport {
                            control: Some((selected.clone(), body.clone())),
                            ..import
                        },
                    );
                }
            }
            Self(Arc::new(Root {
                identity: fresh_identity(),
                entry_call: OnceLock::new(),
                proof_entry: OnceLock::new(),
                transfers: Mutex::new(BTreeMap::new()),
                returns: Mutex::new(BTreeMap::new()),
                c_events: Mutex::new(BTreeMap::new()),
                invocation: self.0.invocation,
                opaque_actor: self.0.opaque_actor,
                pending: self.0.pending.clone(),
                creators: self.0.creators.clone(),
                anchors: self.0.anchors.clone(),
                authority: self.0.authority.clone(),
                scopes: self.0.scopes.clone(),
                exact_members: self.0.exact_members.clone(),
                opaque_types: self.0.opaque_types.clone(),
                symbolic_batches: self.0.symbolic_batches.clone(),
                symbolic_holders: self.0.symbolic_holders.clone(),
                tainted: self.0.tainted.clone(),
                opaque_imports: imports,
                opaque_holders: self.0.opaque_holders.clone(),
                opaque_transfers: Mutex::new(BTreeMap::new()),
                opaque_entry_counts: Mutex::new(BTreeMap::new()),
                empty_populations: self.0.empty_populations.clone(),
            }))
        });
        // The cache key names one explicit resource. A different declaration
        // with that name must not inherit the first declaration's evidence.
        for description in descriptions {
            if let Some(import) = next.0.opaque_imports.get(&description)
                && !import
                    .control
                    .as_ref()
                    .is_some_and(|(fact, body)| fact == selected && body.as_ref() == definition)
            {
                return Err("control registration changed its checked declaration".into());
            }
        }
        Ok(next)
    }

    /// Count shorthand uses the same checked body opening as explicit
    /// `unfold(control)`. No projected memory or authority is published.
    pub(in crate::kernel) fn checked_control_count_permission(
        &self,
        state: &CState,
        description: &ResourceDescription,
        assumptions: &PureFactContext,
    ) -> bool {
        if state.population_effects.creation.as_ref() != Some(self) {
            return false;
        }
        let Some(import) = self.0.opaque_imports.get(description) else {
            return false;
        };
        let Some((selected, definition)) = &import.control else {
            return false;
        };
        !import.retired_authority
            && import.authority_holder == self.0.opaque_actor
            && state
                .checked_authority_wrapper_body(selected, definition, assumptions)
                .is_ok()
    }

    #[cfg(test)]
    pub(in crate::kernel) fn owns_population_member(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        if self.owns_imported_population_member(description) {
            return true;
        }
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return false;
        };
        let Ok(block) = self.exact_member_block(&pointer.pointer().block, description) else {
            return false;
        };
        self.0
            .anchors
            .get(block)
            .and_then(|anchor| {
                self.0
                    .authority
                    .population_at(*anchor, description.family())
            })
            .is_some_and(|population| {
                self.0
                    .authority
                    .holder_owns_member(self.0.invocation, population)
                    || self
                        .0
                        .symbolic_batches
                        .get(&population)
                        .is_some_and(|batch| batch.owner == self.0.invocation)
            })
    }

    pub(in crate::kernel) fn owns_imported_population_member(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        let Some(scope) = self.governing_authority(description) else {
            return false;
        };
        self.0.opaque_imports.get(&scope).is_some_and(|import| {
            if let Some(member) = import
                .private_members
                .get(&Self::exact_count_key(description))
            {
                return member.owner == Some(self.0.opaque_actor);
            }
            if !import.private_members.is_empty() && scope.population_arity().is_some() {
                return false;
            }
            (import
                .wildcard_member
                .as_ref()
                .map_or(import.description == *description, |member| {
                    member == description
                }))
                && (import
                    .member_holders
                    .get(&self.0.opaque_actor)
                    .copied()
                    .unwrap_or(0)
                    > 0
                    || import.symbolic_member_holder == Some(self.0.opaque_actor))
        })
    }

    /// The exact imported populations of one family. Work is linear in the
    /// imports this proof holds, which its contract bounds.
    pub(in crate::kernel) fn imported_populations_of_family(
        &self,
        family: &str,
    ) -> Vec<ResourceDescription> {
        self.0
            .opaque_imports
            .keys()
            .filter(|description| {
                description.family() == family && description.population_arity().is_none()
            })
            .cloned()
            .collect()
    }

    /// Populations imported after `entry`, such as one entered by a typed
    /// mutex acquisition in a standalone helper body. Work is linear in the
    /// imports this proof holds, which its contract and acquisitions bound.
    pub(in crate::kernel) fn opaque_imports_since(&self, entry: &Self) -> Vec<ResourceDescription> {
        self.0
            .opaque_imports
            .keys()
            .filter(|description| !entry.0.opaque_imports.contains_key(description))
            .cloned()
            .collect()
    }

    /// Net checked births and deaths of an exactly imported population,
    /// whoever holds its authority now. Only a birth or death under the
    /// authority changes the owned total, so a later deposit of that authority
    /// into a mutex escrow keeps the recorded change authentic. Symbolic,
    /// private, or named accounting has no such summary and reports `None`.
    pub(in crate::kernel) fn acquired_member_delta(
        &self,
        description: &ResourceDescription,
    ) -> Option<(bool, u32)> {
        let import = self.0.opaque_imports.get(description)?;
        if import.retired_authority
            || import.description != *description
            || import.symbolic_delta.is_some()
            || import.entry_symbolic_members.is_some()
            || !import.private_members.is_empty()
            || !import.named_counts.is_empty()
            || !import.consumed_named.is_empty()
            || !import.born_named.is_empty()
        {
            return None;
        }
        Some((
            import.owned_members >= import.entry_owned_members,
            import.owned_members.abs_diff(import.entry_owned_members),
        ))
    }

    /// Exact signed batch delta from a checked control import. The quantity may
    /// be zero; the direction remains part of the checked transition.
    pub(in crate::kernel) fn imported_member_delta_since_entry(
        &self,
        description: &ResourceDescription,
    ) -> Option<(bool, Bitvector32Term)> {
        // Retirement preserves authenticated transition accounting. Reporting
        // the spent batch here grants no live count read or member custody.
        let scope = self.governing_authority(description)?;
        let import = self.0.opaque_imports.get(&scope)?;
        if let Some(member) = import
            .private_members
            .get(&Self::exact_count_key(description))
        {
            return (!import.retired_authority && import.authority_holder == self.0.opaque_actor)
                .then(|| {
                    (
                        true,
                        Bitvector32Term::Constant(u32::from(member.owner.is_some())),
                    )
                });
        }
        if (scope.population_arity().is_some()
            && import.wildcard_member.as_ref() != Some(description))
            || (scope.population_arity().is_none() && import.description != *description)
            || (!import.retired_authority && import.authority_holder != self.0.opaque_actor)
        {
            return None;
        }
        if import.has_composable_symbolic_birth() {
            return Some((
                true,
                Bitvector32Term::add(
                    import.symbolic_delta.as_ref()?.1.clone(),
                    Bitvector32Term::Constant(import.owned_members),
                ),
            ));
        }
        import.symbolic_delta.clone().or_else(|| {
            if import.entry_symbolic_members.is_some()
                || (import.entry_count.is_none()
                    && import.owned_members == import.entry_owned_members)
            {
                // An unchanged symbolic batch or an unobserved opaque import
                // has no numerical count summary. Preserve that boundary.
                return None;
            }
            if import.entry_owned_members.checked_add(1) == Some(import.owned_members) {
                Some((true, Bitvector32Term::Constant(1)))
            } else if import.owned_members.checked_add(1) == Some(import.entry_owned_members) {
                Some((false, Bitvector32Term::Constant(1)))
            } else {
                Some((
                    import.owned_members >= import.entry_owned_members,
                    Bitvector32Term::Constant(
                        import.owned_members.abs_diff(import.entry_owned_members),
                    ),
                ))
            }
        })
    }

    pub(in crate::kernel) fn spent_imported_member_since(
        &self,
        before: &Self,
        description: &ResourceDescription,
    ) -> bool {
        match (
            before.0.opaque_imports.get(description),
            self.0.opaque_imports.get(description),
        ) {
            (Some(start), Some(end)) => {
                start.description == end.description
                    && end.owned_members.checked_add(1) == Some(start.owned_members)
                    && before.0.opaque_actor == self.0.opaque_actor
            }
            _ => false,
        }
    }

    #[cfg(test)]
    pub(in crate::kernel) fn born_imported_member_since(
        &self,
        before: &Self,
        description: &ResourceDescription,
    ) -> bool {
        match (
            before.0.opaque_imports.get(description),
            self.0.opaque_imports.get(description),
        ) {
            (Some(start), Some(end)) => {
                start.description == end.description
                    && start.owned_members.checked_add(1) == Some(end.owned_members)
                    && before.0.opaque_actor == self.0.opaque_actor
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn retired_imported_authority_since(
        &self,
        before: &Self,
        description: &ResourceDescription,
    ) -> bool {
        match (
            before.0.opaque_imports.get(description),
            self.0.opaque_imports.get(description),
        ) {
            (Some(start), Some(end)) => {
                start.description == end.description
                    && !start.retired_authority
                    && end.retired_authority
                    && end.owned_members == 0
                    && before.0.opaque_actor == self.0.opaque_actor
            }
            _ => false,
        }
    }

    pub(in crate::kernel) fn recognizes_imported_population(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        self.governing_authority(description)
            .is_some_and(|scope| self.0.opaque_imports.contains_key(&scope))
    }

    pub(in crate::kernel) fn recognizes_population_authority(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        self.0.opaque_imports.contains_key(description) || self.tracks_population(description)
    }

    pub(in crate::kernel) fn has_opaque_import(&self) -> bool {
        !self.0.opaque_imports.is_empty()
    }

    /// The description includes the exact pointer; another family or offset
    /// cannot observe this imported count.
    pub(in crate::kernel) fn observe_symbolic(
        &self,
        description: &ResourceDescription,
    ) -> Option<SymbolicPopulationCount> {
        let import = self.0.opaque_imports.get(description)?;
        if import.description != *description
            || import.retired_authority
            || import.authority_holder != self.0.opaque_actor
        {
            return None;
        }
        Some(SymbolicPopulationCount {
            entry_count: import.entry_count.clone()?,
            delta: i32::try_from(import.owned_members)
                .ok()?
                .checked_sub(i32::try_from(import.entry_owned_members).ok()?)?,
            // Only deaths of distinct entry occurrences bound the entry count.
            // Consuming a newly born occurrence contributes no entry bound and
            // neither transition grants anonymous custody in member_holders.
            entry_owned_members: import.entry_owned_members.max(
                import
                    .named_counts
                    .get(description)
                    .map_or(0, |change| change.entry_deaths),
            ),
            entry_symbolic_members: import.entry_symbolic_members.clone(),
            symbolic_delta: import.symbolic_delta.clone(),
        })
    }

    fn adjust_opaque_right(
        &self,
        holder: Holder,
        before: bool,
        after: bool,
    ) -> PersistentMap<Holder, u32> {
        Self::adjust_rights(self.0.opaque_holders.clone(), holder, before, after)
    }

    fn adjust_rights(
        mut holders: PersistentMap<Holder, u32>,
        holder: Holder,
        before: bool,
        after: bool,
    ) -> PersistentMap<Holder, u32> {
        if before == after {
            return holders;
        }
        let count = holders.get(&holder).copied().unwrap_or(0);
        let next = if after {
            count.checked_add(1).expect("opaque rights overflow")
        } else {
            count.checked_sub(1).expect("opaque rights index")
        };
        if next == 0 {
            holders.remove(&holder);
        } else {
            holders.insert(holder, next);
        }
        holders
    }

    fn transfer_opaque(
        &self,
        from: &Self,
        to: &Self,
        description: &ResourceDescription,
        member_description: &ResourceDescription,
        authority_fact: bool,
        quantity: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Result<Self, CreationRefusal> {
        let import = self
            .0
            .opaque_imports
            .get(description)
            .ok_or(CreationRefusal::MissingAuthority)?;
        // Whole symbolic custody can be an unchanged input batch or the exact
        // batch just born under this authority. Moving it changes only its
        // holder, never the population delta or an outstanding owner's rights.
        let symbolic_quantity = if import.symbolic_delta.is_none() {
            import.entry_symbolic_members.as_ref()
        } else if import.entry_symbolic_members.is_none() {
            import
                .symbolic_delta
                .as_ref()
                .filter(|(produce, _)| *produce)
                .map(|(_, quantity)| quantity)
        } else {
            None
        };
        let numeric_custody = quantity.as_const().is_some_and(|quantity| {
            quantity > 0
                && quantity
                    <= import
                        .member_holders
                        .get(&from.0.opaque_actor)
                        .copied()
                        .unwrap_or(0)
        });
        let symbolic_batch = !authority_fact && symbolic_quantity.is_some() && !numeric_custody;
        let quantity = if symbolic_batch {
            if !same_quantity(symbolic_quantity.unwrap(), quantity, assumptions) {
                return Err(CreationRefusal::InvalidQuantity);
            }
            // Numeric batches are bounded by i32::MAX. This disjoint cache tag
            // avoids using a deep symbolic expression as a cache key.
            u32::MAX
        } else {
            quantity
                .as_const()
                .filter(|q| *q > 0 && *q <= i32::MAX as u32)
                .ok_or(if authority_fact {
                    CreationRefusal::InvalidQuantity
                } else {
                    CreationRefusal::MissingMembers
                })?
        };
        let sender = from.0.opaque_actor;
        let receiver = to.0.opaque_actor;
        let key = (
            sender,
            receiver,
            import.identity,
            member_description.clone(),
            authority_fact,
            quantity,
        );
        if let Some(cached) = self
            .0
            .opaque_transfers
            .lock()
            .expect("opaque transfer cache")
            .get(&key)
        {
            return Ok(cached.clone());
        }
        let mut updated = import.clone();
        let mut holders = self.0.opaque_holders.clone();
        if authority_fact {
            if quantity != 1 {
                return Err(CreationRefusal::InvalidQuantity);
            }
            if import.retired_authority || import.authority_holder != sender {
                return Err(CreationRefusal::MissingAuthority);
            }
            updated.authority_holder = receiver;
            if sender != receiver {
                holders = Self::adjust_rights(holders, sender, true, false);
                holders = Self::adjust_rights(holders, receiver, false, true);
            }
        } else if symbolic_batch {
            if import.retired_authority || import.symbolic_member_holder != Some(sender) {
                return Err(CreationRefusal::MissingMembers);
            }
            updated.symbolic_member_holder = Some(receiver);
            if sender != receiver {
                holders = Self::adjust_rights(holders, sender, true, false);
                holders = Self::adjust_rights(holders, receiver, false, true);
            }
        } else {
            if (import.entry_symbolic_members.is_some() || import.symbolic_delta.is_some())
                && !import.has_composable_symbolic_birth()
            {
                return Err(CreationRefusal::InvalidQuantity);
            }
            let private_key = Self::exact_count_key(member_description);
            if let Some(member) = import.private_members.get(&private_key) {
                if quantity != 1 || member.owner != Some(sender) {
                    return Err(CreationRefusal::MissingMembers);
                }
                updated.private_members.insert(
                    private_key,
                    PrivateMember {
                        owner: Some(receiver),
                        ..member.clone()
                    },
                );
            } else if !import.private_members.is_empty() {
                return Err(CreationRefusal::InvalidMember);
            }
            let held = import.member_holders.get(&sender).copied().unwrap_or(0);
            let remaining = held
                .checked_sub(quantity)
                .ok_or(CreationRefusal::MissingMembers)?;
            if sender != receiver {
                let received = import.member_holders.get(&receiver).copied().unwrap_or(0);
                let next = received
                    .checked_add(quantity)
                    .ok_or(CreationRefusal::InvalidQuantity)?;
                updated.member_holders = if remaining == 0 {
                    updated.member_holders.without_key(&sender)
                } else {
                    updated.member_holders.with_inserted(sender, remaining)
                };
                updated.member_holders.insert(receiver, next);
                holders = Self::adjust_rights(holders, sender, held > 0, remaining > 0);
                holders = Self::adjust_rights(holders, receiver, received > 0, next > 0);
            }
        }
        let imports = self
            .0
            .opaque_imports
            .with_inserted(description.clone(), updated);
        let successor = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: holders,
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: imports,
        }));
        Ok(self
            .0
            .opaque_transfers
            .lock()
            .expect("opaque transfer cache")
            .entry(key)
            .or_insert(successor)
            .clone())
    }

    /// Immutable zero evidence from an actual checked empty retirement. This
    /// grants neither resource ownership nor permission to recreate authority.
    pub(in crate::kernel) fn checked_empty_population(
        &self,
        description: &ResourceDescription,
    ) -> bool {
        if let Some(import) = self.0.opaque_imports.get(description) {
            return import.description == *description && import.retired_authority;
        }
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return false;
        };
        let block = &pointer.pointer().block;
        if self.exact_member_block(block, description).is_err() {
            return false;
        }
        self.0
            .empty_populations
            .get(block)
            .is_some_and(|families| families.contains(&description.family().to_owned()))
    }

    /// Recover the declared field schema for an explicit local count pattern.
    /// This indexed type lookup grants no ownership or observation permission.
    pub(in crate::kernel) fn population_type_description(
        &self,
        pattern: &ResourceDescription,
    ) -> ResourceDescription {
        if let Some(description) = self.0.opaque_types.get(pattern) {
            return description.clone();
        }
        let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = pattern.arguments().first() else {
            return pattern.clone();
        };
        self.0
            .scopes
            .get(&(pointer.pointer().block.clone(), pattern.family().to_owned()))
            .filter(|scope| {
                scope.arguments() == pattern.arguments()
                    && scope.population_arity() == pattern.population_arity()
            })
            .cloned()
            .unwrap_or_else(|| pattern.clone())
    }

    /// Resolve one explicit member to its governing scope without enumerating
    /// other pools or members. A scope is not itself a member assertion.
    pub(in crate::kernel) fn governing_authority(
        &self,
        description: &ResourceDescription,
    ) -> Option<ResourceDescription> {
        let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
        else {
            return None;
        };
        if !description.resource_arguments().is_empty() {
            return None;
        }
        crate::instrumentation::record_deterministic_work(1);
        let imported_scope = if description.population_arity().is_some() {
            Some(description.clone())
        } else if description.arguments().len() > 1 {
            ResourceDescription::new(
                description.family().into(),
                vec![description.arguments()[0].clone()].into(),
                description.schema().clone(),
            )
            .with_population_arity(description.arguments().len())
            .ok()
        } else {
            None
        };
        if let Some(scope) = imported_scope
            && self.0.opaque_imports.contains_key(&scope)
        {
            return Some(scope);
        }
        match self
            .0
            .scopes
            .get(&(pointer.pointer().block.clone(), description.family().into()))
        {
            Some(scope) if description == scope => Some(scope.clone()),
            Some(scope)
                if description.population_arity().is_none()
                    && scope.population_arity() == Some(description.arguments().len())
                    && description.arguments().first() == scope.arguments().first()
                    && description.schema() == scope.schema() =>
            {
                Some(scope.clone())
            }
            Some(_) => None,
            None if description.population_arity().is_none()
                && description.arguments().len() == 1 =>
            {
                Some(description.clone())
            }
            None => None,
        }
    }

    fn exact_member_block<'a>(
        &self,
        block: &'a PointerBlock,
        description: &ResourceDescription,
    ) -> Result<&'a PointerBlock, CreationRefusal> {
        let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if pointer.pointer().offset != PointerOffsetTerm::Constant(0)
            || &pointer.pointer().block != block
            || self.governing_authority(description).is_none()
        {
            return Err(CreationRefusal::InvalidMember);
        }
        Ok(block)
    }

    #[cfg(test)]
    /// Read the total only while this proof environment holds the authority.
    pub(in crate::kernel) fn observe(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<u32, CreationRefusal> {
        if *block == PointerBlock::ExternalArgument && !self.0.opaque_imports.is_empty() {
            return Err(CreationRefusal::UnknownTotal);
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, family)
            .ok_or(CreationRefusal::MissingAuthority)?;
        self.0
            .authority
            .observe(self.0.invocation, population)
            .map_err(CreationRefusal::from)
    }

    /// An exact count is global to the family, not the caller's owned quantity.
    /// Concrete keys need decidable identity; imported keys have arbitrary entry
    /// counts and change only when the checked selected member changes.
    pub(in crate::kernel) fn observe_exact_member(
        &self,
        description: &ResourceDescription,
        assumptions: &PureFactContext,
    ) -> Result<SymbolicPopulationCount, CreationRefusal> {
        if description.population_arity().is_some() {
            return Err(CreationRefusal::InvalidMember);
        }
        let scope = self
            .governing_authority(description)
            .filter(|scope| scope.population_arity().is_some())
            .ok_or(CreationRefusal::MissingAuthority)?;
        if !self.owns_population_authority(&scope) {
            return Err(CreationRefusal::MissingAuthority);
        }
        if let Some(import) = self.0.opaque_imports.get(&scope) {
            if let Some(entry) = import.entry_count.clone()
                && import.entry_symbolic_members.is_none()
                && import.symbolic_delta.is_none()
            {
                let delta = i64::from(import.owned_members) - i64::from(import.entry_owned_members);
                let current = if delta >= 0 {
                    Bitvector32Term::add(entry, Bitvector32Term::Constant(delta as u32))
                } else {
                    Bitvector32Term::subtract(entry, Bitvector32Term::Constant((-delta) as u32))
                };
                if crate::kernel::quantity_condition_holds(
                    assumptions,
                    crate::kernel::ConditionTerm::equal(current, Bitvector32Term::Constant(0)),
                ) {
                    return Ok(SymbolicPopulationCount {
                        entry_count: Bitvector32Term::Constant(0),
                        delta: 0,
                        entry_owned_members: 0,
                        entry_symbolic_members: None,
                        symbolic_delta: None,
                    });
                }
            }
            if !scope.schema().is_fieldless() {
                let key = Self::exact_count_key(description);
                if import.named_ambiguous
                    || import
                        .named_selection
                        .as_ref()
                        .is_some_and(|selection| selection != &key)
                {
                    return Err(CreationRefusal::InvalidMember);
                }
                let entry_count = import
                    .exact_entry_counts
                    .lock()
                    .expect("exact entry counts")
                    .entry(key.clone())
                    .or_insert_with(|| {
                        Bitvector32Term::Variable(
                            crate::kernel::Variable::allocate_fresh()
                                .expect("exact count identity exhausted"),
                        )
                    })
                    .clone();
                let change = import.named_counts.get(&key).cloned().unwrap_or_default();
                return Ok(SymbolicPopulationCount {
                    entry_count,
                    delta: change.delta,
                    entry_owned_members: change.entry_deaths,
                    entry_symbolic_members: None,
                    symbolic_delta: None,
                });
            }
            if let Some(member) = import
                .private_members
                .get(&Self::exact_count_key(description))
            {
                if member.owner.is_none()
                    && member.zero_generation != import.private_birth_generation
                {
                    return Err(CreationRefusal::InvalidMember);
                }
                return Ok(SymbolicPopulationCount {
                    entry_count: Bitvector32Term::Constant(u32::from(member.owner.is_some())),
                    delta: 0,
                    entry_owned_members: 0,
                    entry_symbolic_members: None,
                    symbolic_delta: None,
                });
            }
            if !import.private_members.is_empty() {
                return Err(CreationRefusal::InvalidMember);
            }
            let selected = import.wildcard_member.as_ref();
            let matches = selected.is_some_and(|member| {
                member
                    .arguments()
                    .iter()
                    .zip(description.arguments())
                    .all(|(a, b)| crate::kernel::resource_arguments_proven_equal(a, b, assumptions))
            });
            // The initial authority-only entry may describe a future birth.
            // Once a member is selected, do not assume another potentially
            // aliased index was unaffected by its exchange.
            if selected.is_some() && !matches {
                return Err(CreationRefusal::InvalidMember);
            }
            let key = Self::exact_count_key(selected.filter(|_| matches).unwrap_or(description));
            let entry_count = import
                .exact_entry_counts
                .lock()
                .expect("exact entry counts")
                .entry(key)
                .or_insert_with(|| {
                    Bitvector32Term::Variable(
                        crate::kernel::Variable::allocate_fresh()
                            .expect("exact count identity exhausted"),
                    )
                })
                .clone();
            return Ok(SymbolicPopulationCount {
                entry_count,
                delta: if matches {
                    i32::try_from(import.owned_members)
                        .ok()
                        .and_then(|n| n.checked_sub(import.entry_owned_members as i32))
                        .ok_or(CreationRefusal::InvalidQuantity)?
                } else {
                    0
                },
                entry_owned_members: if matches {
                    import.entry_owned_members
                } else {
                    0
                },
                entry_symbolic_members: None,
                symbolic_delta: None,
            });
        }
        let [AlgebraicValue::C(CValue::Pointer(anchor))] = scope.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        if self
            .observed_symbolic_batch(&anchor.pointer().block, scope.family())
            .is_some()
        {
            return Err(CreationRefusal::UnknownTotal);
        }
        let unresolved = self
            .0
            .exact_members
            .get(&Self::exact_count_key(&scope))
            .copied()
            .unwrap_or(0)
            != 0;
        let empty = self
            .observe_term(&anchor.pointer().block, scope.family())?
            .as_const()
            == Some(0);
        if (!Self::has_concrete_indices(description) || unresolved) && !empty {
            return Err(CreationRefusal::InvalidMember);
        }
        Ok(SymbolicPopulationCount {
            entry_count: Bitvector32Term::Constant(if empty {
                0
            } else {
                self.0
                    .exact_members
                    .get(&Self::exact_count_key(description))
                    .copied()
                    .unwrap_or(0)
            }),
            delta: 0,
            entry_owned_members: 0,
            entry_symbolic_members: None,
            symbolic_delta: None,
        })
    }

    fn exact_count_key(description: &ResourceDescription) -> ResourceDescription {
        // Casts, qualifiers, and equivalent constant expressions preserve
        // resource index identity. The key never includes C pointee metadata.
        description.map_values(|value| match value {
            AlgebraicValue::C(CValue::Pointer(pointer)) => {
                let mut address = pointer.pointer().clone();
                if let Some(offset) = address.offset.as_const() {
                    address.offset = PointerOffsetTerm::Constant(offset);
                }
                AlgebraicValue::C(CValue::pointer(address))
            }
            AlgebraicValue::C(CValue::Int32(value)) => AlgebraicValue::C(CValue::Int32(
                value
                    .as_const()
                    .map(Bitvector32Term::Constant)
                    .unwrap_or_else(|| value.clone()),
            )),
            other => other.clone(),
        })
    }

    fn has_concrete_indices(description: &ResourceDescription) -> bool {
        description.arguments().iter().all(|value| match value {
            AlgebraicValue::C(CValue::Pointer(pointer)) => {
                matches!(pointer.pointer().block, PointerBlock::Heap(_))
                    || pointer.pointer().block.starts_with("local:")
            }
            AlgebraicValue::C(CValue::Int32(value)) => value.as_const().is_some(),
            _ => false,
        }) && description.arguments().iter().all(|value| match value {
            AlgebraicValue::C(CValue::Pointer(pointer)) => {
                pointer.pointer().offset.as_const().is_some()
            }
            _ => true,
        })
    }

    /// Observe the exact concrete-anchor total, including one outstanding
    /// symbolic batch, only while this holder owns population authority.
    pub(in crate::kernel) fn observe_term(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Bitvector32Term, CreationRefusal> {
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, family)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let base = self
            .0
            .authority
            .observe(self.0.invocation, population)
            .map_err(CreationRefusal::from)?;
        let base = Bitvector32Term::Constant(base);
        Ok(match self.0.symbolic_batches.get(&population) {
            Some(batch) => Bitvector32Term::add(base, batch.quantity.clone()),
            None => base,
        })
    }

    pub(in crate::kernel) fn observed_symbolic_batch(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Option<(u32, Bitvector32Term)> {
        let anchor = *self.0.anchors.get(block)?;
        let population = self.0.authority.population_at(anchor, family)?;
        let base = self
            .0
            .authority
            .observe(self.0.invocation, population)
            .ok()?;
        let batch = self.0.symbolic_batches.get(&population)?;
        Some((base, batch.quantity.clone()))
    }

    /// Exchange a checked quantity of one resource family. Symbolic batches are
    /// admitted for opaque helper proofs only; a concrete anchor still uses the
    /// exact cardinality engine below.
    /// The caller checks the ordinary body exchange and a fixed positive
    /// exclusive footprint. That footprint rules out a second equal instance.
    pub(in crate::kernel) fn checked_exclusive_member_exchange_quantity(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
        produce: bool,
        quantity: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Result<(Self, CheckedPopulationMemberExchange), CreationRefusal> {
        if quantity.as_const() != Some(1) {
            return Err(CreationRefusal::InvalidQuantity);
        }
        self.checked_member_exchange_with_context(
            block,
            description,
            produce,
            Some(assumptions),
            1,
            MemberForm::Quantity {
                exclusive_body: true,
            },
        )
    }

    pub(in crate::kernel) fn checked_member_exchange_quantity(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
        produce: bool,
        quantity: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Result<(Self, CheckedPopulationMemberExchange), CreationRefusal> {
        if !description.schema().is_fieldless() {
            // Named occurrences carry independent fields, not an anonymous
            // quantity that can be produced without those owned instances.
            return Err(CreationRefusal::InvalidMember);
        }
        // A birth with an authenticated exact numeric value uses the numeric
        // ledger. Bounds alone cannot choose a member quantity, and existing
        // symbolic input custody keeps its original representation on spend.
        let exact_numeric = produce
            .then(|| crate::kernel::assumptions::exact_signed_constant(quantity, assumptions))
            .flatten()
            .filter(|value| (0..=i64::from(i32::MAX)).contains(value))
            .map(|value| Bitvector32Term::Constant(value as u32));
        let quantity = exact_numeric.as_ref().unwrap_or(quantity);
        // A helper may select the complete numerical batch by an entry field
        // rather than a literal. Keep the symbolic-batch path unchanged.
        let numerical = (!produce && quantity.as_const().is_none())
            .then(|| self.0.opaque_imports.get(description))
            .flatten()
            .filter(|import| {
                import.entry_symbolic_members.is_none() && import.symbolic_delta.is_none()
            })
            .and_then(|import| {
                numerical_batch_quantity(
                    quantity,
                    import
                        .member_holders
                        .get(&self.0.opaque_actor)
                        .copied()
                        .unwrap_or(0),
                    assumptions,
                )
            })
            .map(Bitvector32Term::Constant);
        let quantity = numerical.as_ref().unwrap_or(quantity);
        if quantity.as_const() == Some(1) {
            return self.checked_member_exchange_with_context(
                block,
                description,
                produce,
                Some(assumptions),
                1,
                MemberForm::Quantity {
                    exclusive_body: false,
                },
            );
        }
        // Locally established concrete batches use the same numerical custody
        // as unit exchanges. A literal batch must not become indivisible
        // symbolic custody just because its amount is greater than one.
        if let Some(amount) = quantity.as_const().filter(|n| *n <= i32::MAX as u32)
            && self
                .governing_authority(description)
                .is_some_and(|scope| !self.0.opaque_imports.contains_key(&scope))
        {
            return self.checked_member_exchange_with_context(
                block,
                description,
                produce,
                Some(assumptions),
                amount,
                MemberForm::Quantity {
                    exclusive_body: false,
                },
            );
        }
        // Concrete batches in opaque unary populations share the numerical
        // ledger with unit operations. Updating a batch is constant work, not
        // one exchange per unit, and may be followed by checked helper calls.
        if let Some(amount) = quantity
            .as_const()
            .filter(|amount| *amount <= i32::MAX as u32)
            && let Some(import) = self.0.opaque_imports.get(description)
            && (import.entry_symbolic_members.is_none() && import.symbolic_delta.is_none()
                || import.has_composable_symbolic_birth())
            && description.population_arity().is_none()
        {
            if produce && amount > 0 && !import.has_composable_symbolic_birth() {
                let entry = import
                    .entry_count
                    .clone()
                    .ok_or(CreationRefusal::UnknownTotal)?;
                let delta = i64::from(import.owned_members) - i64::from(import.entry_owned_members);
                let zero_entry =
                    assumptions.exact_condition_value(&crate::kernel::ConditionTerm::equal(
                        entry.clone(),
                        Bitvector32Term::Constant(0),
                    )) == Some(true);
                let upper = entry
                    .as_const()
                    .map(|value| i64::from(value as i32))
                    .or_else(|| {
                        assumptions
                            .indexed_constant_interval(&entry)
                            .map(|(_, high)| high)
                    });
                let bounded = (zero_entry && delta + i64::from(amount) <= i64::from(i32::MAX))
                    || upper.is_some_and(|high| {
                        high + delta + i64::from(amount) <= i64::from(i32::MAX)
                    });
                let current = if delta >= 0 {
                    Bitvector32Term::add(entry, Bitvector32Term::Constant(delta as u32))
                } else {
                    Bitvector32Term::subtract(entry, Bitvector32Term::Constant((-delta) as u32))
                };
                if !bounded
                    && assumptions.exact_condition_value(
                        &crate::kernel::ConditionTerm::signed_add_overflows(
                            current,
                            quantity.clone(),
                        ),
                    ) != Some(false)
                {
                    return Err(CreationRefusal::InvalidQuantity);
                }
            }
            return self.checked_member_exchange_with_context(
                block,
                description,
                produce,
                Some(assumptions),
                amount,
                MemberForm::Quantity {
                    exclusive_body: false,
                },
            );
        }
        if !crate::kernel::quantity_condition_holds(
            assumptions,
            crate::kernel::ConditionTerm::signed_greater_equal(
                quantity.clone(),
                Bitvector32Term::Constant(0),
            ),
        ) {
            return Err(CreationRefusal::InvalidQuantity);
        }
        if self.0.opaque_imports.get(description).is_none() {
            self.exact_member_block(block, description)?;
            let anchor = *self
                .0
                .anchors
                .get(block)
                .ok_or(CreationRefusal::MissingAuthority)?;
            let population = self
                .0
                .authority
                .population_at(anchor, description.family())
                .ok_or(CreationRefusal::MissingAuthority)?;
            if !self
                .0
                .authority
                .holder_owns_authority(self.0.invocation, population)
            {
                return Err(CreationRefusal::MissingAuthority);
            }
            let mut batches = self.0.symbolic_batches.clone();
            let mut holders = self.0.symbolic_holders.clone();
            if produce {
                if batches.contains_key(&population) {
                    return Err(CreationRefusal::OutstandingMembers);
                }
                let base = self
                    .0
                    .authority
                    .observe(self.0.invocation, population)
                    .map_err(CreationRefusal::from)?;
                let maximum = Bitvector32Term::Constant(i32::MAX as u32 - base);
                if !crate::kernel::quantity_condition_holds(
                    assumptions,
                    crate::kernel::ConditionTerm::signed_greater_equal(maximum, quantity.clone()),
                ) {
                    return Err(CreationRefusal::InvalidQuantity);
                }
                batches.insert(
                    population,
                    SymbolicBatch {
                        owner: self.0.invocation,
                        quantity: quantity.clone(),
                    },
                );
                let held = holders.get(&self.0.invocation).copied().unwrap_or(0);
                holders.insert(
                    self.0.invocation,
                    held.checked_add(1)
                        .ok_or(CreationRefusal::InvalidQuantity)?,
                );
            } else {
                let batch = batches
                    .get(&population)
                    .ok_or(CreationRefusal::MissingMembers)?;
                if batch.owner != self.0.invocation
                    || !same_quantity(&batch.quantity, quantity, assumptions)
                {
                    return Err(CreationRefusal::MissingMembers);
                }
                batches.remove(&population);
                let held = holders.get(&self.0.invocation).copied().unwrap_or(0);
                if held <= 1 {
                    holders.remove(&self.0.invocation);
                } else {
                    holders.insert(self.0.invocation, held - 1);
                }
            }
            let mut tainted = self.0.tainted.clone();
            if produce {
                let families = tainted
                    .get(block)
                    .cloned()
                    .unwrap_or_default()
                    .with_value(description.family().to_owned());
                tainted.insert(block.clone(), families);
            }
            let after = Self(Arc::new(Root {
                identity: fresh_identity(),
                entry_call: OnceLock::new(),
                proof_entry: OnceLock::new(),
                transfers: Mutex::new(BTreeMap::new()),
                returns: Mutex::new(BTreeMap::new()),
                c_events: Mutex::new(BTreeMap::new()),
                invocation: self.0.invocation,
                opaque_actor: self.0.opaque_actor,
                pending: self.0.pending.clone(),
                creators: self.0.creators.clone(),
                anchors: self.0.anchors.clone(),
                authority: self.0.authority.clone(),
                symbolic_batches: batches,
                symbolic_holders: holders,
                tainted,
                opaque_holders: self.0.opaque_holders.clone(),
                opaque_transfers: Mutex::new(BTreeMap::new()),
                opaque_entry_counts: Mutex::new(BTreeMap::new()),
                empty_populations: self.0.empty_populations.clone(),
                scopes: self.0.scopes.clone(),
                exact_members: self.0.exact_members.clone(),
                opaque_types: self.0.opaque_types.clone(),
                opaque_imports: self.0.opaque_imports.clone(),
            }));
            let evidence = CheckedPopulationMemberExchange {
                before: self.0.identity,
                after: after.0.identity,
                description: description.clone(),
                produce,
            };
            return Ok((after, evidence));
        }
        let import = self
            .0
            .opaque_imports
            .get(description)
            .filter(|import| import.entry_count.is_some())
            .ok_or(CreationRefusal::MissingAuthority)?;
        if import.retired_authority || import.authority_holder != self.0.opaque_actor {
            return Err(CreationRefusal::MissingAuthority);
        }
        // Successive births can extend the actor's own freshly created batch.
        // Imported entry custody and batches held by another actor remain
        // indivisible; a count observation cannot substitute for that custody.
        let symbolic_delta = if import.symbolic_delta.is_some() {
            if !import.has_composable_symbolic_birth()
                || import.symbolic_member_holder != Some(self.0.opaque_actor)
            {
                return Err(CreationRefusal::InvalidQuantity);
            }
            let Some((true, prior)) = &import.symbolic_delta else {
                return Err(CreationRefusal::InvalidQuantity);
            };
            if produce {
                let current = self
                    .observe_symbolic(description)
                    .and_then(|count| {
                        Some(Bitvector32Term::add(
                            count.entry_count.clone(),
                            count.combined_delta()?.1,
                        ))
                    })
                    .ok_or(CreationRefusal::MissingAuthority)?;
                if assumptions.exact_condition_value(
                    &crate::kernel::ConditionTerm::signed_add_overflows(current, quantity.clone()),
                ) != Some(false)
                {
                    return Err(CreationRefusal::InvalidQuantity);
                }
                Some((true, Bitvector32Term::add(prior.clone(), quantity.clone())))
            } else {
                if !same_quantity(prior, quantity, assumptions) {
                    return Err(CreationRefusal::InvalidQuantity);
                }
                // Retiring the entire owned birth cancels only its symbolic delta.
                // Entry observations and separately held numerical members remain.
                None
            }
        } else {
            Some((produce, quantity.clone()))
        };
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        if &pointer.pointer().block != block {
            return Err(CreationRefusal::InvalidMember);
        }
        if produce {
            if import.owned_members != 0 || import.entry_symbolic_members.is_some() {
                return Err(CreationRefusal::MissingMembers);
            }
        } else if (import.entry_symbolic_members.as_ref() != Some(quantity)
            && !import.has_composable_symbolic_birth())
            || import.symbolic_member_holder != Some(self.0.opaque_actor)
        {
            return Err(CreationRefusal::MissingMembers);
        }
        let after = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.adjust_opaque_right(
                self.0.opaque_actor,
                import.entry_symbolic_members.is_some() || import.symbolic_delta.is_some(),
                produce,
            ),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.with_inserted(
                description.clone(),
                OpaqueImport {
                    symbolic_delta,
                    symbolic_member_holder: produce.then_some(self.0.opaque_actor),
                    ..import.clone()
                },
            ),
        }));
        let evidence = CheckedPopulationMemberExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            produce,
        };
        Ok((after, evidence))
    }

    #[cfg(test)]
    /// Change exactly one member. The caller supplies a checked resource type;
    /// this method independently rejects fields, references and non-base anchors.
    pub(in crate::kernel) fn checked_member_exchange(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
        produce: bool,
    ) -> Result<(Self, CheckedPopulationMemberExchange), CreationRefusal> {
        self.checked_member_exchange_with_context(
            block,
            description,
            produce,
            None,
            1,
            MemberForm::Quantity {
                exclusive_body: false,
            },
        )
    }

    /// The checked resource rewrite supplies one held named occurrence. This
    /// records its death without manufacturing anonymous custody from a count.
    pub(in crate::kernel) fn checked_imported_instance_consumption(
        &self,
        instance: &crate::kernel::ResourceInstance,
    ) -> Result<Self, CreationRefusal> {
        self.checked_imported_instance_exchange(instance, false, &PureFactContext::new())
    }

    pub(in crate::kernel) fn checked_imported_instance_exchange(
        &self,
        instance: &crate::kernel::ResourceInstance,
        produce: bool,
        assumptions: &PureFactContext,
    ) -> Result<Self, CreationRefusal> {
        let reference = ResourceReference::from_instance(instance);
        let description = reference.description();
        if description.population_arity().is_some()
            || description.schema().is_fieldless()
            || !description.resource_arguments().is_empty()
        {
            return Err(CreationRefusal::InvalidMember);
        }
        let scope = self
            .governing_authority(description)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let import = self
            .0
            .opaque_imports
            .get(&scope)
            .filter(|import| import.entry_count.is_some())
            .ok_or(CreationRefusal::MissingAuthority)?;
        if import.retired_authority || import.authority_holder != self.0.opaque_actor {
            return Err(CreationRefusal::MissingAuthority);
        }
        let key = CEvent::InstanceMember(reference.clone(), produce);
        if let Some(existing) = self.0.c_events.lock().expect("C event cache").get(&key) {
            return Ok(existing.clone());
        }
        if import.consumed_named.contains_key(&instance.identity()) {
            return Err(CreationRefusal::MissingMembers);
        }
        if produce && import.born_named.contains_key(&instance.identity()) {
            return Err(CreationRefusal::InvalidMember);
        }
        let aggregate = import.named_counts.get(&scope).cloned().unwrap_or_default();
        if produce {
            let entry = import
                .entry_count
                .clone()
                .ok_or(CreationRefusal::UnknownTotal)?;
            let current = if aggregate.delta >= 0 {
                Bitvector32Term::add(
                    entry.clone(),
                    Bitvector32Term::Constant(aggregate.delta as u32),
                )
            } else {
                Bitvector32Term::subtract(
                    entry.clone(),
                    Bitvector32Term::Constant(aggregate.delta.unsigned_abs()),
                )
            };
            let overflow = crate::kernel::ConditionTerm::signed_add_overflows(
                current,
                Bitvector32Term::Constant(1),
            );
            if assumptions.exact_condition_value(&overflow) != Some(false)
                && !assumptions
                    .indexed_constant_interval(&entry)
                    .is_some_and(|(_, high)| {
                        high + i64::from(aggregate.delta) < i64::from(i32::MAX)
                    })
            {
                return Err(CreationRefusal::InvalidQuantity);
            }
        }
        let entry_death = !produce && !import.born_named.contains_key(&instance.identity());
        let advance = |before: NamedCountChange| -> Result<NamedCountChange, CreationRefusal> {
            Ok(NamedCountChange {
                delta: before
                    .delta
                    .checked_add(if produce { 1 } else { -1 })
                    .ok_or(CreationRefusal::InvalidQuantity)?,
                entry_deaths: before
                    .entry_deaths
                    .checked_add(u32::from(entry_death))
                    .filter(|n| *n <= i32::MAX as u32)
                    .ok_or(CreationRefusal::InvalidQuantity)?,
            })
        };
        let aggregate = advance(aggregate)?;
        let mut named_counts = import
            .named_counts
            .with_inserted(scope.clone(), aggregate.clone());
        let exact = Self::exact_count_key(description);
        if scope.population_arity().is_some() {
            let change = advance(import.named_counts.get(&exact).cloned().unwrap_or_default())?;
            named_counts.insert(exact.clone(), change);
        }
        let unresolved = description.arguments().iter().skip(1).any(|value| {
            !matches!(value, AlgebraicValue::C(CValue::Int32(value)) if value.as_const().is_some())
        });
        let named_ambiguous = import.named_ambiguous
            || import
                .named_selection
                .as_ref()
                .is_some_and(|selection| selection != &exact)
            || unresolved
                && !import.named_counts.is_empty()
                && !import.named_counts.contains_key(&exact);
        let named_selection = import
            .named_selection
            .clone()
            .or_else(|| unresolved.then_some(exact));
        let consumed_named = if produce {
            import.consumed_named.clone()
        } else {
            import
                .consumed_named
                .with_inserted(instance.identity(), Arc::new(instance.clone()))
        };
        let born_named = if produce {
            import.born_named.with_inserted(instance.identity(), ())
        } else {
            import.born_named.clone()
        };
        let after = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.with_inserted(
                scope.clone(),
                OpaqueImport {
                    symbolic_delta: (aggregate.delta != 0).then(|| {
                        (
                            aggregate.delta > 0,
                            Bitvector32Term::Constant(aggregate.delta.unsigned_abs()),
                        )
                    }),
                    consumed_named,
                    born_named,
                    named_counts,
                    named_selection,
                    named_ambiguous,
                    ..import.clone()
                },
            ),
        }));
        Ok(self
            .0
            .c_events
            .lock()
            .expect("C event cache")
            .entry(key)
            .or_insert(after)
            .clone())
    }

    /// A checked death is a boundary receipt, never current instance custody.
    pub(in crate::kernel) fn consumed_imported_instance(
        &self,
        description: &ResourceDescription,
        identity: crate::kernel::Variable,
    ) -> Option<&crate::kernel::ResourceInstance> {
        let scope = self.governing_authority(description)?;
        let import = self.0.opaque_imports.get(&scope)?;
        if import.retired_authority || import.authority_holder != self.0.opaque_actor {
            return None;
        }
        import.consumed_named.get(&identity).map(AsRef::as_ref)
    }

    /// Advance the local ledger for one separately owned occurrence. Its
    /// reference retains identity and type arguments, never observed fields.
    /// Resource ownership and the body exchange are checked by the caller.
    pub(in crate::kernel) fn checked_instance_exchange(
        &self,
        reference: &ResourceReference,
        produce: bool,
    ) -> Result<Self, CreationRefusal> {
        let description = reference.description();
        let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if description.population_arity().is_some()
            || !description.resource_arguments().is_empty()
            || self.recognizes_imported_population(description)
        {
            return Err(CreationRefusal::InvalidMember);
        }
        let key = CEvent::InstanceMember(reference.clone(), produce);
        if let Some(existing) = self.0.c_events.lock().expect("C event cache").get(&key) {
            return Ok(existing.clone());
        }
        let (next, _) = self.checked_member_exchange_with_context(
            &pointer.pointer().block,
            description,
            produce,
            None,
            1,
            MemberForm::Instance,
        )?;
        Ok(self
            .0
            .c_events
            .lock()
            .expect("C event cache")
            .entry(key)
            .or_insert(next)
            .clone())
    }

    fn checked_member_exchange_with_context(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
        produce: bool,
        assumptions: Option<&PureFactContext>,
        amount: u32,
        form: MemberForm,
    ) -> Result<(Self, CheckedPopulationMemberExchange), CreationRefusal> {
        let exclusive_body = matches!(
            form,
            MemberForm::Quantity {
                exclusive_body: true
            }
        );
        if description.population_arity().is_some()
            || matches!(form, MemberForm::Quantity { .. }) && !description.schema().is_fieldless()
        {
            return Err(CreationRefusal::InvalidMember);
        }
        let scope = self
            .governing_authority(description)
            .ok_or(CreationRefusal::InvalidMember)?;
        if let Some(import) = self.0.opaque_imports.get(&scope) {
            let private_key = Self::exact_count_key(description);
            let private = import.private_members.get(&private_key);
            let private_exchange = scope.population_arity().is_some()
                && (private.is_some() || exclusive_body && produce);
            if scope.population_arity().is_some() {
                if amount != 1 {
                    return Err(CreationRefusal::InvalidQuantity);
                }
                if private_exchange {
                    if produce {
                        if private.is_some_and(|member| member.owner.is_some())
                            || import.wildcard_member.is_some() && import.owned_members != 0
                        {
                            return Err(CreationRefusal::InvalidMember);
                        }
                    } else if private.and_then(|member| member.owner) != Some(self.0.opaque_actor) {
                        return Err(CreationRefusal::MissingMembers);
                    }
                } else if produce {
                    if import.wildcard_member.is_some() || import.owned_members != 0 {
                        return Err(CreationRefusal::InvalidMember);
                    }
                } else if import.owned_members != 1
                    || import.wildcard_member.as_ref() != Some(description)
                {
                    return Err(CreationRefusal::InvalidMember);
                }
                if produce {
                    let entry = import
                        .entry_count
                        .clone()
                        .ok_or(CreationRefusal::UnknownTotal)?;
                    let delta =
                        i64::from(import.owned_members) - i64::from(import.entry_owned_members);
                    let total = if delta >= 0 {
                        Bitvector32Term::add(entry.clone(), Bitvector32Term::Constant(delta as u32))
                    } else {
                        Bitvector32Term::subtract(
                            entry.clone(),
                            Bitvector32Term::Constant((-delta) as u32),
                        )
                    };
                    let no_overflow = crate::kernel::ConditionTerm::signed_add_overflows(
                        total,
                        Bitvector32Term::Constant(1),
                    );
                    if !assumptions.is_some_and(|facts| {
                        facts.exact_condition_value(&no_overflow) == Some(false)
                            || facts
                                .indexed_constant_interval(&entry)
                                .is_some_and(|(_, high)| high + delta < i64::from(i32::MAX))
                            || entry
                                .as_const()
                                .is_some_and(|n| i64::from(n as i32) + delta < i64::from(i32::MAX))
                    }) {
                        return Err(CreationRefusal::InvalidQuantity);
                    }
                }
            }
            // A born symbolic batch and separately held numerical fragments
            // retain independent custody. The count summary composes both deltas.
            if import.entry_symbolic_members.is_some() || import.symbolic_delta.is_some() {
                if scope.population_arity().is_some() || !import.has_composable_symbolic_birth() {
                    return Err(CreationRefusal::InvalidQuantity);
                }
                if produce && amount > 0 {
                    let current = self
                        .observe_symbolic(&scope)
                        .and_then(|count| {
                            Some(Bitvector32Term::add(
                                count.entry_count.clone(),
                                count.combined_delta()?.1,
                            ))
                        })
                        .ok_or(CreationRefusal::MissingAuthority)?;
                    let condition = crate::kernel::ConditionTerm::signed_add_overflows(
                        current.clone(),
                        Bitvector32Term::Constant(amount),
                    );
                    if !assumptions.is_some_and(|facts| {
                        facts.exact_condition_value(&condition) == Some(false)
                            || facts
                                .indexed_constant_interval(&current)
                                .is_some_and(|(_, high)| {
                                    high + i64::from(amount) <= i64::from(i32::MAX)
                                })
                            || PureFactContext::decide_intrinsically(&condition) == Some(false)
                    }) {
                        return Err(CreationRefusal::InvalidQuantity);
                    }
                }
            }
            // Opaque custody follows only checked exact contract transfers;
            // numeric exchanges change the global fragment total separately.
            let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
            else {
                return Err(CreationRefusal::InvalidMember);
            };
            if &pointer.pointer().block != block {
                return Err(CreationRefusal::InvalidMember);
            }
            if import.retired_authority || import.authority_holder != self.0.opaque_actor {
                return Err(CreationRefusal::MissingAuthority);
            }
            let held = import
                .member_holders
                .get(&self.0.opaque_actor)
                .copied()
                .unwrap_or(0);
            let next_held = if produce {
                held.checked_add(amount)
            } else {
                held.checked_sub(amount)
            }
            .ok_or(CreationRefusal::MissingMembers)?;
            let owned_members = if produce {
                import
                    .owned_members
                    .checked_add(amount)
                    .filter(|n| *n <= i32::MAX as u32)
            } else {
                import.owned_members.checked_sub(amount)
            }
            .ok_or(if produce {
                CreationRefusal::PopulationCountOverflow
            } else {
                CreationRefusal::MissingMembers
            })?;
            let mut private_members = import.private_members.clone();
            let private_birth_generation = if private_exchange && produce {
                import
                    .private_birth_generation
                    .checked_add(1)
                    .ok_or(CreationRefusal::InvalidQuantity)?
            } else {
                import.private_birth_generation
            };
            if private_exchange {
                private_members.insert(
                    private_key,
                    PrivateMember {
                        owner: produce.then_some(self.0.opaque_actor),
                        zero_generation: private_birth_generation,
                    },
                );
            }
            let after = Self(Arc::new(Root {
                identity: fresh_identity(),
                entry_call: OnceLock::new(),
                proof_entry: OnceLock::new(),
                transfers: Mutex::new(BTreeMap::new()),
                returns: Mutex::new(BTreeMap::new()),
                c_events: Mutex::new(BTreeMap::new()),
                invocation: self.0.invocation,
                opaque_actor: self.0.opaque_actor,
                pending: self.0.pending.clone(),
                creators: self.0.creators.clone(),
                anchors: self.0.anchors.clone(),
                authority: self.0.authority.clone(),
                symbolic_batches: self.0.symbolic_batches.clone(),
                symbolic_holders: self.0.symbolic_holders.clone(),
                tainted: self.0.tainted.clone(),
                opaque_holders: self.adjust_opaque_right(
                    self.0.opaque_actor,
                    held > 0,
                    next_held > 0,
                ),
                opaque_transfers: Mutex::new(BTreeMap::new()),
                opaque_entry_counts: Mutex::new(BTreeMap::new()),
                empty_populations: self.0.empty_populations.clone(),
                scopes: self.0.scopes.clone(),
                exact_members: self.0.exact_members.clone(),
                opaque_types: self.0.opaque_types.clone(),
                opaque_imports: self.0.opaque_imports.with_inserted(
                    scope.clone(),
                    OpaqueImport {
                        private_members,
                        private_birth_generation,
                        wildcard_member: if scope.population_arity().is_some() && !private_exchange
                        {
                            Some(description.clone())
                        } else {
                            import.wildcard_member.clone()
                        },
                        owned_members,
                        member_holders: if next_held == 0 {
                            import.member_holders.without_key(&self.0.opaque_actor)
                        } else {
                            import
                                .member_holders
                                .with_inserted(self.0.opaque_actor, next_held)
                        },
                        ..import.clone()
                    },
                ),
            }));
            let evidence = CheckedPopulationMemberExchange {
                before: self.0.identity,
                after: after.0.identity,
                description: description.clone(),
                produce,
            };
            return Ok((after, evidence));
        }
        self.exact_member_block(block, description)?;
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, description.family())
            .ok_or(CreationRefusal::MissingAuthority)?;
        if self.0.symbolic_batches.contains_key(&population) {
            return Err(CreationRefusal::InvalidQuantity);
        }
        let authority = if amount == 0 {
            if !self
                .0
                .authority
                .holder_owns_authority(self.0.invocation, population)
            {
                return Err(CreationRefusal::MissingAuthority);
            }
            self.0.authority.clone()
        } else if produce {
            self.0
                .authority
                .produce(self.0.invocation, population, amount)
                .map_err(CreationRefusal::from)?
        } else {
            self.0
                .authority
                .consume(self.0.invocation, population, amount)
                .map_err(CreationRefusal::from)?
        };
        let mut exact_members = self.0.exact_members.clone();
        if scope.population_arity().is_some() {
            let key = Self::exact_count_key(description);
            let scope_key = Self::exact_count_key(&scope);
            if !Self::has_concrete_indices(description) {
                // Preserve existing symbolic-member exchanges. Once identities
                // are unresolved, exact absence stays unavailable until the
                // entire population is empty; no unrelated key scan is needed.
                exact_members.insert(scope_key, 1);
            } else if exact_members.get(&scope_key).copied().unwrap_or(0) == 0 {
                let prior = exact_members.get(&key).copied().unwrap_or(0);
                let next = if produce {
                    prior.checked_add(amount)
                } else {
                    prior.checked_sub(amount)
                }
                .ok_or(CreationRefusal::MissingMembers)?;
                exact_members.insert(key, next);
            }
        }
        let mut tainted = self.0.tainted.clone();
        if produce {
            let families = tainted
                .get(block)
                .cloned()
                .unwrap_or_default()
                .with_value(description.family().to_owned());
            tainted.insert(block.clone(), families);
        }
        let after = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted,
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members,
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        }));
        let evidence = CheckedPopulationMemberExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            produce,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn new() -> Self {
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: Holder::fresh(),
            opaque_actor: Holder::fresh(),
            pending: PersistentMap::default(),
            creators: PersistentMap::default(),
            anchors: PersistentMap::default(),
            authority: AuthorityState::default(),
            symbolic_batches: PersistentMap::default(),
            symbolic_holders: PersistentMap::default(),
            tainted: PersistentMap::default(),
            opaque_holders: PersistentMap::default(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: PersistentMap::default(),
            scopes: PersistentMap::default(),
            exact_members: PersistentMap::default(),
            opaque_types: PersistentMap::default(),
            opaque_imports: PersistentMap::default(),
        }))
    }

    /// A call carries known storage origins but runs in a distinct creator
    /// environment. The caller's current creation rights do not follow it.
    /// Rechecking one entry must recover exactly the same child identity.
    /// Distinct C call occurrences need their own event key before calls are
    /// enabled.
    pub(in crate::kernel) fn enter_call(&self) -> Self {
        self.0
            .entry_call
            .get_or_init(|| {
                Self(Arc::new(Root {
                    identity: fresh_identity(),
                    entry_call: OnceLock::new(),
                    proof_entry: OnceLock::new(),
                    transfers: Mutex::new(BTreeMap::new()),
                    returns: Mutex::new(BTreeMap::new()),
                    c_events: Mutex::new(BTreeMap::new()),
                    invocation: Holder::fresh(),
                    opaque_actor: Holder::fresh(),
                    pending: self.0.pending.clone(),
                    creators: self.0.creators.clone(),
                    anchors: self.0.anchors.clone(),
                    authority: self.0.authority.clone(),
                    symbolic_batches: self.0.symbolic_batches.clone(),
                    symbolic_holders: self.0.symbolic_holders.clone(),
                    tainted: self.0.tainted.clone(),
                    opaque_holders: self.0.opaque_holders.clone(),
                    opaque_transfers: Mutex::new(BTreeMap::new()),
                    opaque_entry_counts: Mutex::new(BTreeMap::new()),
                    empty_populations: self.0.empty_populations.clone(),
                    scopes: self.0.scopes.clone(),
                    exact_members: self.0.exact_members.clone(),
                    opaque_types: self.0.opaque_types.clone(),
                    opaque_imports: self.0.opaque_imports.clone(),
                }))
            })
            .clone()
    }

    /// Rebind a standalone proof's declared input to its checked function
    /// entry. Unlike an ordinary nested call, this retains the one opaque
    /// assumption that the proof entry itself is required to establish.
    pub(in crate::kernel) fn enter_proof_entry(&self) -> Self {
        self.0
            .proof_entry
            .get_or_init(|| {
                Self(Arc::new(Root {
                    identity: fresh_identity(),
                    entry_call: OnceLock::new(),
                    proof_entry: OnceLock::new(),
                    transfers: Mutex::new(BTreeMap::new()),
                    returns: Mutex::new(BTreeMap::new()),
                    c_events: Mutex::new(BTreeMap::new()),
                    invocation: Holder::fresh(),
                    opaque_actor: self.0.opaque_actor,
                    pending: self.0.pending.clone(),
                    creators: self.0.creators.clone(),
                    anchors: self.0.anchors.clone(),
                    authority: self.0.authority.clone(),
                    symbolic_batches: self.0.symbolic_batches.clone(),
                    symbolic_holders: self.0.symbolic_holders.clone(),
                    tainted: self.0.tainted.clone(),
                    opaque_holders: self.0.opaque_holders.clone(),
                    opaque_transfers: Mutex::new(BTreeMap::new()),
                    opaque_entry_counts: Mutex::new(BTreeMap::new()),
                    empty_populations: self.0.empty_populations.clone(),
                    scopes: self.0.scopes.clone(),
                    exact_members: self.0.exact_members.clone(),
                    opaque_types: self.0.opaque_types.clone(),
                    opaque_imports: self.0.opaque_imports.clone(),
                }))
            })
            .clone()
    }

    /// Move one exact owned contract fact between invocation holders. The
    /// visible resource planner must perform the matching owned exchange;
    /// this ledger operation changes neither the population total nor C memory.
    pub(in crate::kernel) fn transfer_call_fact(
        &self,
        from: &Self,
        to: &Self,
        description: &ResourceDescription,
        authority_fact: bool,
    ) -> Result<Self, CreationRefusal> {
        self.transfer_call_fact_quantity(
            from,
            to,
            description,
            authority_fact,
            &Bitvector32Term::Constant(1),
            &PureFactContext::new(),
        )
    }

    pub(in crate::kernel) fn transfer_call_fact_quantity(
        &self,
        from: &Self,
        to: &Self,
        description: &ResourceDescription,
        authority_fact: bool,
        quantity: &Bitvector32Term,
        assumptions: &PureFactContext,
    ) -> Result<Self, CreationRefusal> {
        let scope = self.governing_authority(description);
        let numerical = (!authority_fact && quantity.as_const().is_none())
            .then(|| {
                scope
                    .as_ref()
                    .and_then(|scope| self.0.opaque_imports.get(scope))
            })
            .flatten()
            .filter(|import| {
                import.entry_symbolic_members.is_none() && import.symbolic_delta.is_none()
            })
            .and_then(|import| {
                numerical_batch_quantity(
                    quantity,
                    import
                        .member_holders
                        .get(&from.0.opaque_actor)
                        .copied()
                        .unwrap_or(0),
                    assumptions,
                )
            })
            .map(Bitvector32Term::Constant);
        let quantity = numerical.as_ref().unwrap_or(quantity);
        // Zero ownership transports no member capability, including when a
        // checked contract equality establishes that a field-valued quantity
        // is zero. It cannot move the authority or justify a unit operation.
        if !authority_fact && same_quantity(quantity, &Bitvector32Term::Constant(0), assumptions) {
            return Ok(self.clone());
        }
        if let Some(scope) = scope
            && let Some(import) = self.0.opaque_imports.get(&scope)
        {
            if import.wildcard_member.is_some()
                && !import
                    .private_members
                    .contains_key(&Self::exact_count_key(description))
                && if authority_fact {
                    description != &scope
                } else {
                    import.wildcard_member.as_ref() != Some(description)
                }
            {
                return Err(CreationRefusal::InvalidMember);
            }
            return self.transfer_opaque(
                from,
                to,
                &scope,
                description,
                authority_fact,
                quantity,
                assumptions,
            );
        }
        let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        let block = self.exact_member_block(&pointer.pointer().block, description)?;
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let population = self
            .0
            .authority
            .population_at(anchor, description.family())
            .ok_or(CreationRefusal::MissingAuthority)?;
        let key = (
            from.0.invocation,
            to.0.invocation,
            population,
            authority_fact,
            quantity.clone(),
        );
        if let Some(cached) = self.0.transfers.lock().expect("transfer cache").get(&key) {
            return Ok(cached.clone());
        }
        let mut batches = self.0.symbolic_batches.clone();
        let mut holders = self.0.symbolic_holders.clone();
        let authority = if authority_fact {
            if quantity.as_const() != Some(1) {
                return Err(CreationRefusal::InvalidQuantity);
            }
            self.0
                .authority
                .transfer_authority(from.0.invocation, to.0.invocation, population)
                .map_err(CreationRefusal::from)?
        } else if let Some(batch) = batches.get(&population).cloned() {
            if batch.owner != from.0.invocation
                || !same_quantity(&batch.quantity, quantity, assumptions)
            {
                return Err(CreationRefusal::MissingMembers);
            }
            if from.0.invocation != to.0.invocation {
                batches.insert(
                    population,
                    SymbolicBatch {
                        owner: to.0.invocation,
                        quantity: batch.quantity,
                    },
                );
                let prior = holders.get(&from.0.invocation).copied().unwrap_or(0);
                if prior <= 1 {
                    holders.remove(&from.0.invocation);
                } else {
                    holders.insert(from.0.invocation, prior - 1);
                }
                let received = holders.get(&to.0.invocation).copied().unwrap_or(0);
                holders.insert(
                    to.0.invocation,
                    received
                        .checked_add(1)
                        .ok_or(CreationRefusal::InvalidQuantity)?,
                );
            }
            self.0.authority.clone()
        } else if let Some(exact) = quantity
            .as_const()
            .filter(|q| *q > 0 && *q <= i32::MAX as u32)
        {
            self.0
                .authority
                .transfer_members(from.0.invocation, to.0.invocation, population, exact)
                .map_err(CreationRefusal::from)?
        } else {
            return Err(CreationRefusal::MissingMembers);
        };
        let successor = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: batches,
            symbolic_holders: holders,
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        }));
        Ok(self
            .0
            .transfers
            .lock()
            .expect("transfer cache")
            .entry(key)
            .or_insert(successor)
            .clone())
    }

    /// Move the C storage cleanup obligation with a consumed or borrowed
    /// control whose checked body contains the allocation. The ordinary
    /// resource transfer separately moves that exact allocation fact.
    pub(in crate::kernel) fn tracks_storage_anchor(&self, block: &PointerBlock) -> bool {
        self.0.anchors.contains_key(block)
    }

    pub(in crate::kernel) fn transfer_call_anchor(
        &self,
        from: &Self,
        to: &Self,
        block: &PointerBlock,
    ) -> Result<Self, CreationRefusal> {
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::MissingAuthority)?;
        let authority = self
            .0
            .authority
            .transfer_anchor(from.0.invocation, to.0.invocation, anchor)
            .map_err(CreationRefusal::from)?;
        Ok(self.memoized_c_event(
            CEvent::TransferredAnchor(from.0.invocation, to.0.invocation, block.clone()),
            || {
                Self(Arc::new(Root {
                    identity: fresh_identity(),
                    entry_call: OnceLock::new(),
                    proof_entry: OnceLock::new(),
                    transfers: Mutex::new(BTreeMap::new()),
                    returns: Mutex::new(BTreeMap::new()),
                    c_events: Mutex::new(BTreeMap::new()),
                    invocation: self.0.invocation,
                    opaque_actor: self.0.opaque_actor,
                    pending: self.0.pending.clone(),
                    creators: self.0.creators.clone(),
                    anchors: self.0.anchors.clone(),
                    authority,
                    symbolic_batches: self.0.symbolic_batches.clone(),
                    symbolic_holders: self.0.symbolic_holders.clone(),
                    tainted: self.0.tainted.clone(),
                    opaque_holders: self.0.opaque_holders.clone(),
                    opaque_transfers: Mutex::new(BTreeMap::new()),
                    opaque_entry_counts: Mutex::new(BTreeMap::new()),
                    empty_populations: self.0.empty_populations.clone(),
                    scopes: self.0.scopes.clone(),
                    exact_members: self.0.exact_members.clone(),
                    opaque_types: self.0.opaque_types.clone(),
                    opaque_imports: self.0.opaque_imports.clone(),
                }))
            },
        ))
    }

    pub(in crate::kernel) fn tracks_population(&self, description: &ResourceDescription) -> bool {
        if self.recognizes_imported_population(description) {
            return true;
        }
        let Some(AlgebraicValue::C(CValue::Pointer(pointer))) = description.arguments().first()
        else {
            return false;
        };
        if self.governing_authority(description).is_none() {
            return false;
        }
        self.0
            .anchors
            .get(&pointer.pointer().block)
            .and_then(|anchor| {
                self.0
                    .authority
                    .population_at(*anchor, description.family())
            })
            .is_some()
    }

    /// A helper can finish only after returning or consuming all abstract
    /// ownership it received. In particular it cannot strand a member while
    /// returning the authority, or retain a creator anchor from local storage.
    pub(in crate::kernel) fn finish_call(&self, caller: &Self) -> Result<Self, CreationRefusal> {
        if self.0.opaque_holders.contains_key(&self.0.opaque_actor)
            || self.0.symbolic_holders.contains_key(&self.0.invocation)
        {
            return Err(CreationRefusal::OutstandingOwnership);
        }
        self.0
            .authority
            .finish_holder(self.0.invocation)
            .map_err(CreationRefusal::from)?;
        Ok(self.return_to(caller))
    }

    /// Return keeps creation events from the callee but restores the caller's
    /// environment. A callee-created object cannot be established by caller.
    pub(in crate::kernel) fn return_to(&self, caller: &Self) -> Self {
        if let Some(cached) = self
            .0
            .returns
            .lock()
            .expect("return cache")
            .get(&caller.0.identity)
        {
            return cached.clone();
        }
        let successor = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: caller.0.invocation,
            opaque_actor: caller.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        }));
        self.0
            .returns
            .lock()
            .expect("return cache")
            .entry(caller.0.identity)
            .or_insert(successor)
            .clone()
    }

    /// The C `malloc`/`calloc` statement owns an unresolved result. Record
    /// its creator before another function can test the pointer and resolve
    /// the outcome. This is not yet a live-storage creation grant.
    pub(in crate::kernel) fn pending_creation(&self, block: PointerBlock) -> Self {
        self.memoized_c_event(CEvent::Pending(block.clone()), || {
            self.pending_creation_uncached(block)
        })
    }

    fn pending_creation_uncached(&self, block: PointerBlock) -> Self {
        debug_assert!(matches!(&block, PointerBlock::Symbolic(_)));
        assert!(
            !self.0.pending.contains_key(&block),
            "pending allocation reused"
        );
        let mut pending = self.0.pending.clone();
        pending.insert(block, self.0.invocation);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending,
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        }))
    }

    /// Resolve an actual pending allocation. Failure discards its origin;
    /// success attaches the original creator to the trusted Heap block even
    /// when a helper made the deciding branch.
    pub(in crate::kernel) fn resolve_pending(
        &self,
        pending_block: &PointerBlock,
        live_block: Option<PointerBlock>,
    ) -> Self {
        self.memoized_c_event(
            CEvent::Resolve(pending_block.clone(), live_block.clone()),
            || self.resolve_pending_uncached(pending_block, live_block),
        )
    }

    fn resolve_pending_uncached(
        &self,
        pending_block: &PointerBlock,
        live_block: Option<PointerBlock>,
    ) -> Self {
        let Some(creator) = self.0.pending.get(pending_block).copied() else {
            return self.clone();
        };
        let mut pending = self.0.pending.clone();
        pending.remove(pending_block);
        let mut creators = self.0.creators.clone();
        let mut anchors = self.0.anchors.clone();
        let mut authority = self.0.authority.clone();
        let mut empty_populations = self.0.empty_populations.clone();
        let mut tainted = self.0.tainted.without_key(pending_block);
        if let Some(block) = live_block {
            empty_populations.remove(&block);
            debug_assert!(matches!(&block, PointerBlock::Heap(_)));
            assert!(
                !creators.contains_key(&block),
                "storage lifetime created twice"
            );
            if let Some(families) = self.0.tainted.get(pending_block) {
                tainted.insert(block.clone(), families.clone());
            }
            let (next, anchor) = authority.allocate_anchor(creator);
            authority = next;
            anchors.insert(block.clone(), anchor);
            creators.insert(block, creator);
        }
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending,
            creators,
            anchors,
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted,
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations,
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        }))
    }

    /// Called only at checked C storage creation, never at resource lowering,
    /// contract allocation import, or generic memory-block construction.
    pub(in crate::kernel) fn created(&self, block: PointerBlock) -> Self {
        self.memoized_c_event(CEvent::Created(block.clone()), || {
            self.created_uncached(block)
        })
    }

    fn created_uncached(&self, block: PointerBlock) -> Self {
        debug_assert!(matches!(block, PointerBlock::Heap(_)) || block.starts_with("local:"));
        let mut creators = self.0.creators.clone();
        assert!(
            !creators.contains_key(&block),
            "storage lifetime created twice"
        );
        let (authority, anchor) = self.0.authority.allocate_anchor(self.0.invocation);
        let mut anchors = self.0.anchors.clone();
        anchors.insert(block.clone(), anchor);
        creators.insert(block.clone(), self.0.invocation);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators,
            anchors,
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.without_key(&block),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        }))
    }

    pub(in crate::kernel) fn created_here(&self, block: &PointerBlock) -> bool {
        self.0.creators.get(block).copied() == Some(self.0.invocation)
    }

    pub(in crate::kernel) fn retirement_refusal(
        &self,
        block: &PointerBlock,
    ) -> Option<CreationRefusal> {
        let anchor = *self.0.anchors.get(block)?;
        self.0
            .authority
            .free_anchor(self.0.invocation, anchor)
            .err()
            .map(CreationRefusal::from)
    }

    /// Once a member existed, absence from the local resource context is no
    /// evidence of an empty population: it may have been transferred away.
    /// This mark follows the storage lifetime across helper calls.
    pub(in crate::kernel) fn member_created(&self, block: &PointerBlock, family: &str) -> Self {
        if !self.0.creators.contains_key(block) && !self.0.pending.contains_key(block) {
            return self.clone();
        }
        self.memoized_c_event(
            CEvent::MemberCreated(block.clone(), family.to_owned()),
            || self.member_created_uncached(block, family),
        )
    }

    fn member_created_uncached(&self, block: &PointerBlock, family: &str) -> Self {
        if !self.0.creators.contains_key(block) && !self.0.pending.contains_key(block) {
            return self.clone();
        }
        let mut tainted = self.0.tainted.clone();
        let families = tainted
            .get(block)
            .cloned()
            .unwrap_or_default()
            .with_value(family.to_owned());
        tainted.insert(block.clone(), families);
        Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted,
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        }))
    }

    #[cfg(test)]
    /// A checked source fold may establish only at its own creation event,
    /// before any member of this family has existed in the storage lifetime.
    pub(in crate::kernel) fn establish(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Self, CreationRefusal> {
        self.establish_scoped(block, family, None)
    }

    fn establish_scoped(
        &self,
        block: &PointerBlock,
        family: &str,
        scope: Option<&ResourceDescription>,
    ) -> Result<Self, CreationRefusal> {
        if !self.created_here(block) {
            return Err(CreationRefusal::NotCreationEnvironment);
        }
        if self
            .0
            .tainted
            .get(block)
            .is_some_and(|families| families.contains(&family.to_owned()))
        {
            return Err(CreationRefusal::MembersAlreadyExisted);
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let (authority, _) = self
            .0
            .authority
            .establish(self.0.invocation, anchor, family)
            .map_err(CreationRefusal::from)?;
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            scopes: match scope {
                Some(scope) => self
                    .0
                    .scopes
                    .with_inserted((block.clone(), family.into()), scope.clone()),
                None => self.0.scopes.clone(),
            },
            opaque_imports: self.0.opaque_imports.clone(),
        })))
    }

    pub(in crate::kernel) fn checked_establish(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        let [AlgebraicValue::C(CValue::Pointer(pointer))] = description.arguments() else {
            return Err(CreationRefusal::InvalidMember);
        };
        if &pointer.pointer().block != block
            || pointer.pointer().offset != PointerOffsetTerm::Constant(0)
            || !description.resource_arguments().is_empty()
        {
            return Err(CreationRefusal::InvalidMember);
        }
        let after = self.establish_scoped(block, description.family(), Some(description))?;
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: true,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn checked_retire(
        &self,
        block: &PointerBlock,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        self.exact_member_block(block, description)?;
        let after = self.retire_authority(block, description.family())?;
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: false,
        };
        Ok((after, evidence))
    }

    /// Require both exhausted member custody and a proof that the current
    /// authenticated global count is zero. Local exhaustion alone never
    /// establishes that no other members exist.
    pub(in crate::kernel) fn check_imported_retirement(
        &self,
        description: &ResourceDescription,
        assumptions: &PureFactContext,
    ) -> Result<(), CreationRefusal> {
        let import = self
            .0
            .opaque_imports
            .get(description)
            .ok_or(CreationRefusal::MissingAuthority)?;
        if import.retired_authority || import.authority_holder != self.0.opaque_actor {
            return Err(CreationRefusal::MissingAuthority);
        }
        if import.owned_members != 0
            || import
                .symbolic_delta
                .as_ref()
                .map_or(import.entry_symbolic_members.is_some(), |(produce, _)| {
                    *produce
                })
        {
            return Err(CreationRefusal::OutstandingMembers);
        }
        let symbolic = self
            .observe_symbolic(description)
            .ok_or(CreationRefusal::UnknownTotal)?;
        // With no remaining custody, the delta is the consumed batch (or
        // the exhausted numeric inputs). Equality to that entry total is a
        // direct zero proof; an explicit current-count-zero fact also works.
        let consumed = symbolic
            .symbolic_delta
            .map(|(_, quantity)| quantity)
            .unwrap_or(Bitvector32Term::Constant(symbolic.delta.unsigned_abs()));
        let current = Bitvector32Term::subtract(symbolic.entry_count.clone(), consumed.clone());
        if !same_quantity(&symbolic.entry_count, &consumed, assumptions)
            && !same_quantity(&current, &Bitvector32Term::Constant(0), assumptions)
        {
            return Err(CreationRefusal::UnknownTotal);
        }
        Ok(())
    }

    pub(in crate::kernel) fn checked_retire_imported(
        &self,
        description: &ResourceDescription,
        assumptions: &PureFactContext,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        self.check_imported_retirement(description, assumptions)?;
        let import = self
            .0
            .opaque_imports
            .get(description)
            .expect("checked import");
        let after = Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority: self.0.authority.clone(),
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.adjust_opaque_right(self.0.opaque_actor, true, false),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.with_inserted(
                description.clone(),
                OpaqueImport {
                    retired_authority: true,
                    ..import.clone()
                },
            ),
        }));
        let evidence = CheckedPopulationAuthorityExchange {
            before: self.0.identity,
            after: after.0.identity,
            description: description.clone(),
            establish: false,
        };
        Ok((after, evidence))
    }

    pub(in crate::kernel) fn retire_authority(
        &self,
        block: &PointerBlock,
        family: &str,
    ) -> Result<Self, CreationRefusal> {
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let population = self
            .0
            .authority
            .population_at(anchor, family)
            .ok_or(CreationRefusal::MissingAuthority)?;
        if self.0.symbolic_batches.contains_key(&population) {
            return Err(CreationRefusal::OutstandingMembers);
        }
        let authority = self
            .0
            .authority
            .retire(self.0.invocation, population)
            .map_err(CreationRefusal::from)?;
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators: self.0.creators.clone(),
            anchors: self.0.anchors.clone(),
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.with_inserted(
                block.clone(),
                self.0
                    .empty_populations
                    .get(block)
                    .cloned()
                    .unwrap_or_default()
                    .with_value(family.to_owned()),
            ),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        })))
    }

    /// End of an automatic or heap lifetime removes its provenance. Future
    /// reuse at the same address needs an independently checked creation.
    pub(in crate::kernel) fn retired(&self, block: &PointerBlock) -> Result<Self, CreationRefusal> {
        if !self.0.creators.contains_key(block) {
            return Ok(self.clone());
        }
        if let Some(refusal) = self.retirement_refusal(block) {
            return Err(refusal);
        }
        Ok(self.memoized_c_event(CEvent::Retired(block.clone()), || {
            self.retired_uncached(block)
                .expect("retirement was checked before memoizing")
        }))
    }

    fn retired_uncached(&self, block: &PointerBlock) -> Result<Self, CreationRefusal> {
        if !self.0.creators.contains_key(block) {
            return Ok(self.clone());
        }
        let anchor = *self
            .0
            .anchors
            .get(block)
            .ok_or(CreationRefusal::NotCreationEnvironment)?;
        let authority = self
            .0
            .authority
            .free_anchor(self.0.invocation, anchor)
            .map_err(CreationRefusal::from)?;
        let mut creators = self.0.creators.clone();
        creators.remove(block);
        let mut anchors = self.0.anchors.clone();
        anchors.remove(block);
        Ok(Self(Arc::new(Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            c_events: Mutex::new(BTreeMap::new()),
            invocation: self.0.invocation,
            opaque_actor: self.0.opaque_actor,
            pending: self.0.pending.clone(),
            creators,
            anchors,
            authority,
            symbolic_batches: self.0.symbolic_batches.clone(),
            symbolic_holders: self.0.symbolic_holders.clone(),
            tainted: self.0.tainted.without_key(block),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
            scopes: self.0.scopes.clone(),
            exact_members: self.0.exact_members.clone(),
            opaque_types: self.0.opaque_types.clone(),
            opaque_imports: self.0.opaque_imports.clone(),
        })))
    }
}

#[cfg(test)]
mod tests;
