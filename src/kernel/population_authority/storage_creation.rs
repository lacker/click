//! Creation history of C storage created by the executing proof environment.
//!
//! This optional event ledger binds abstract population authority to checked
//! C storage creation. It grants no C memory permission, and assumed
//! allocation claims never enter it.

use super::{Anchor, AuthorityState, Holder, Refusal};
use crate::kernel::{
    AddressBase, AddressOffset, AlgebraicValue, CompositeResourceDefinition, ExecutionState,
    OldMachineTerm, ProgramValue, PureFactContext, Resource, ResourceDescription, ResourceFact,
    ResourceReference,
};
use crate::kernel::{OffsetTree, OffsetView};
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
    left: &OldMachineTerm,
    right: &OldMachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || crate::kernel::quantity_comparison_holds(
            assumptions,
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::CompareRelation::Equal,
            left,
            right,
        )
}

/// Resolve a numerical request from its literal or exact recorded value, or
/// an equality with the sender's complete batch. The caller checks custody;
/// neither a global count nor a bound can supply missing member rights.
fn numerical_batch_quantity(
    quantity: &OldMachineTerm,
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
            (assumptions.exact_condition_value(&crate::kernel::OldConditionTerm::equal(
                quantity.clone(),
                OldMachineTerm::constant(held),
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
    /// which no storage created earlier in this proof can alias. It carries
    /// the program point the lock started from, which names its total.
    Acquired(Option<crate::kernel::program_point::ProgramPointId>),
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
        Mutex<BTreeMap<(Holder, Holder, super::Population, bool, OldMachineTerm), CreationEvents>>,
    returns: Mutex<BTreeMap<u64, CreationEvents>>,
    storage_events: Mutex<BTreeMap<StorageEvent, CreationEvents>>,
    invocation: Holder,
    /// Standalone proof entry preserves only declared opaque custody; the C
    /// invocation remains fresh and cannot inherit storage creation rights.
    opaque_actor: Holder,
    pending: PersistentMap<AddressBase, Holder>,
    creators: PersistentMap<AddressBase, Holder>,
    anchors: PersistentMap<AddressBase, Anchor>,
    authority: AuthorityState,
    scopes: PersistentMap<(AddressBase, String), ResourceDescription>,
    /// Exact identities in concrete wildcard populations; totals remain in AuthorityState.
    exact_members: PersistentMap<ResourceDescription, u32>,
    opaque_types: PersistentMap<ResourceDescription, ResourceDescription>,
    /// One symbolic member batch per live population, with its owning holder.
    symbolic_batches: PersistentMap<super::Population, SymbolicBatch>,
    symbolic_holders: PersistentMap<Holder, u32>,
    /// Per-storage family history; never inferred from the current owner.
    tainted: PersistentMap<AddressBase, PersistentSet<String>>,
    /// Exact declared population inputs. Each carries no creator right,
    /// storage event, or asserted total.
    opaque_imports: PersistentMap<ResourceDescription, OpaqueImport>,
    /// Number of authority/member fragments held by each opaque actor.
    /// Call completion checks this index without visiting unrelated imports.
    opaque_holders: PersistentMap<Holder, u32>,
    opaque_transfers:
        Mutex<BTreeMap<(Holder, Holder, u64, ResourceDescription, bool, u32), CreationEvents>>,
    opaque_entry_counts: Mutex<BTreeMap<ResourceDescription, OldMachineTerm>>,
    empty_populations: PersistentMap<AddressBase, PersistentSet<String>>,
}

#[derive(Clone)]
struct SymbolicBatch {
    owner: Holder,
    quantity: OldMachineTerm,
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
    exact_entry_counts: Arc<Mutex<BTreeMap<ResourceDescription, OldMachineTerm>>>,
    /// The checked definition used to open this exact entry control for a
    /// read-only count observation. Current ownership is checked on each read.
    control: Option<(ResourceFact, Arc<CompositeResourceDefinition>)>,
    entry_owned_members: u32,
    owned_members: u32,
    /// Symbolic cardinality is admitted only through a checked control wrapper.
    entry_symbolic_members: Option<OldMachineTerm>,
    /// Whole-batch custody is independent of the authority holder.
    symbolic_member_holder: Option<Holder>,
    symbolic_delta: Option<(bool, OldMachineTerm)>,
    /// Occurrences consumed by checked named rewrites, independent of count observations.
    consumed_named: PersistentMap<crate::kernel::InstanceId, Arc<crate::kernel::ResourceInstance>>,
    /// Named births remain distinct from entry occurrences, even after death.
    born_named: PersistentMap<crate::kernel::InstanceId, ()>,
    named_counts: PersistentMap<ResourceDescription, NamedCountChange>,
    /// Unresolved indices permit exact observation only of this single selection.
    named_selection: Option<ResourceDescription>,
    named_ambiguous: bool,
    /// Only a checked control wrapper can supply this immutable entry load.
    entry_count: Option<OldMachineTerm>,
    /// For a total acquired with a lock rather than at entry, the program
    /// point the lock started from.
    acquired_at: Option<crate::kernel::program_point::ProgramPointId>,
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
    pub entry_count: OldMachineTerm,
    pub delta: i32,
    pub entry_owned_members: u32,
    pub entry_symbolic_members: Option<OldMachineTerm>,
    pub symbolic_delta: Option<(bool, OldMachineTerm)>,
}

impl SymbolicPopulationCount {
    pub(in crate::kernel) fn entry_lower_bound(&self) -> crate::kernel::Proposition {
        let numerical = OldMachineTerm::constant(self.entry_owned_members);
        let owned = self.entry_symbolic_members.as_ref().unwrap_or(&numerical);
        let bound =
            crate::kernel::StoredConditionTerm::signed_int32_at_least(&self.entry_count, owned);
        crate::kernel::Proposition::condition_is(bound, true)
    }

    /// Preserve both components of a checked symbolic birth followed by
    /// numerical births. Other mixed directions are not admitted by the ledger.
    pub(in crate::kernel) fn combined_delta(&self) -> Option<(bool, OldMachineTerm)> {
        match (&self.symbolic_delta, self.delta) {
            (Some((true, quantity)), delta) if delta > 0 => Some((
                true,
                OldMachineTerm::add(quantity.clone(), OldMachineTerm::constant(delta as u32)),
            )),
            (Some(delta), _) => Some(delta.clone()),
            (None, delta) if delta != 0 => {
                Some((delta > 0, OldMachineTerm::constant(delta.unsigned_abs())))
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
enum StorageEvent {
    Control(ResourceFact),
    Pending(AddressBase),
    Resolve(AddressBase, Option<AddressBase>),
    Created(AddressBase),
    MemberCreated(AddressBase, String),
    Retired(AddressBase),
    InstanceMember(ResourceReference, bool),
    TransferredAnchor(Holder, Holder, AddressBase),
    AcquiredControl(
        ResourceDescription,
        u32,
        Option<crate::kernel::program_point::ProgramPointId>,
    ),
}

/// Whether a population anchor is a caller-supplied pointer, governed by an
/// opaque import rather than by an anchor this execution created.
///
/// A pointer read is named by its read rather than spelled in the storage
/// block it was read from; it is external exactly when that storage is, as
/// the storage-block spelling of the same read was.
pub(in crate::kernel) fn is_external_population_anchor(anchor: &crate::kernel::Address) -> bool {
    match &anchor.base {
        AddressBase::ExternalArgument => true,
        AddressBase::Load(load) | AddressBase::SliceData(load) => {
            load.cell().base == AddressBase::ExternalArgument
        }
        _ => false,
    }
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

impl std::fmt::Display for CreationRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::NotCreationEnvironment => {
                "this transition is not in a checked creation scope for the population"
            }
            Self::MembersAlreadyExisted => {
                "members of the population already existed before it was created"
            }
            Self::AlreadyEstablished => {
                "the population was already established at this anchor and cannot be established again"
            }
            Self::MissingAuthority => "the population's authority is not held here",
            Self::MissingMembers => "fewer members of the population are held than the transition moves",
            Self::InvalidMember => "the resource is not a member of a population",
            Self::InvalidQuantity => "a member quantity must be between 1 and INT_MAX",
            Self::PopulationCountOverflow => "the population count would exceed int32",
            Self::OutstandingMembers => {
                "members of the population are still outstanding, so its authority cannot be retired"
            }
            Self::OutstandingAuthority => {
                "an authority registered at this anchor is still outstanding"
            }
            Self::OutstandingOwnership => {
                "population control, members or an anchor would be discarded at scope exit"
            }
            Self::UnknownTotal => "the population's total is not known here",
            Self::OpaqueImportConflict => {
                "an imported opaque population conflicts with one already held"
            }
        })
    }
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
    /// The next ledger: a fresh identity and empty memo caches, with every
    /// recorded field carried over. Each transition overrides the fields it
    /// changes with struct-update syntax.
    fn successor(&self) -> Root {
        Root {
            identity: fresh_identity(),
            entry_call: OnceLock::new(),
            proof_entry: OnceLock::new(),
            transfers: Mutex::new(BTreeMap::new()),
            returns: Mutex::new(BTreeMap::new()),
            storage_events: Mutex::new(BTreeMap::new()),
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
            opaque_imports: self.0.opaque_imports.clone(),
            opaque_holders: self.0.opaque_holders.clone(),
            opaque_transfers: Mutex::new(BTreeMap::new()),
            opaque_entry_counts: Mutex::new(BTreeMap::new()),
            empty_populations: self.0.empty_populations.clone(),
        }
    }

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

    fn memoized_storage_event(&self, key: StorageEvent, create: impl FnOnce() -> Self) -> Self {
        if let Some(existing) = self
            .0
            .storage_events
            .lock()
            .expect("C event cache")
            .get(&key)
        {
            return existing.clone();
        }
        let next = create();
        self.0
            .storage_events
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
        acquired_at: Option<crate::kernel::program_point::ProgramPointId>,
    ) -> Result<Self, CreationRefusal> {
        let key = StorageEvent::AcquiredControl(description.clone(), owned_members, acquired_at);
        if let Some(existing) = self
            .0
            .storage_events
            .lock()
            .expect("C event cache")
            .get(&key)
        {
            return Ok(existing.clone());
        }
        let next = self.import_opaque_contract_population_with_member(
            description,
            owned_members,
            Some(self.fresh_opaque_entry_count(description)?),
            None,
            None,
            OpaqueMemberInputs::Acquired(acquired_at),
        )?;
        Ok(self.memoized_storage_event(key, || next))
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
            &OldMachineTerm::constant(owned_members),
        )
    }

    /// The arbitrary entry total of an opaque import, stable across rechecks
    /// of the same ledger.
    fn fresh_opaque_entry_count(
        &self,
        description: &ResourceDescription,
    ) -> Result<OldMachineTerm, CreationRefusal> {
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
                OldMachineTerm::Variable(
                    crate::kernel::Variable::allocate_fresh()
                        .expect("opaque count identity exhausted"),
                )
            })
            .clone())
    }

    pub(in crate::kernel) fn import_observable_contract_population_quantity(
        &self,
        description: &ResourceDescription,
        quantity: &OldMachineTerm,
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
                    OldMachineTerm::Variable(
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
                    OldMachineTerm::Variable(
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
        state: &ExecutionState,
        selected: &ResourceFact,
        definition: &CompositeResourceDefinition,
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
        state: &ExecutionState,
        selected: &ResourceFact,
        definition: &CompositeResourceDefinition,
        assumptions: &PureFactContext,
        wildcard_members: &BTreeMap<ResourceDescription, Vec<ResourceFact>>,
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
                            let count = OldMachineTerm::Variable(variable);
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
                        let ResourceFact::Own(Resource::Composite { name, arguments }, quantity) =
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
            let member = Resource::Composite {
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
                .map_err(|refusal| format!("control import refused: {refusal}"))?;
        }
        Ok(events)
    }

    fn import_opaque_contract_population_inner(
        &self,
        description: &ResourceDescription,
        owned_members: u32,
        entry_count: Option<OldMachineTerm>,
        symbolic_members: Option<OldMachineTerm>,
        control: Option<(ResourceFact, Arc<CompositeResourceDefinition>)>,
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
        entry_count: Option<OldMachineTerm>,
        symbolic_members: Option<OldMachineTerm>,
        control: Option<(ResourceFact, Arc<CompositeResourceDefinition>)>,
        members: OpaqueMemberInputs,
    ) -> Result<Self, CreationRefusal> {
        let named_authority = matches!(members, OpaqueMemberInputs::NamedAuthority);
        let acquired_at = match members {
            OpaqueMemberInputs::Acquired(point) => point,
            _ => None,
        };
        let acquired = matches!(members, OpaqueMemberInputs::Acquired(_));
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
            OpaqueMemberInputs::NamedAuthority | OpaqueMemberInputs::Acquired(_) => None,
        };
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
            (description.arguments()).fixed_values::<1>()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if (description.population_arity().is_none() && wildcard_member.is_some())
            || !is_external_population_anchor(pointer.address())
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
        if let Some(OldMachineTerm::Variable(variable)) = &entry_count {
            crate::kernel::model_fields::register_population_entry_count(
                *variable,
                crate::kernel::model_fields::PopulationEntryCount {
                    family: Arc::from(description.family()),
                    anchor: pointer.address().clone(),
                    wildcards: description.population_arity().map_or(0, |arity| arity - 1),
                    member: None,
                },
            );
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
                acquired_at,
                retired_authority: false,
            },
        );
        Ok(Self(Arc::new(Root {
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
            opaque_types: if named_authority {
                self.0
                    .opaque_types
                    .with_inserted(pattern, description.clone())
            } else {
                self.0.opaque_types.clone()
            },
            opaque_imports,
            ..self.successor()
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
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
            (description.arguments()).fixed_values::<1>()
        else {
            return false;
        };
        let Ok(block) = self.exact_member_block(&pointer.address().base, description) else {
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
        state: &ExecutionState,
        selected: &ResourceFact,
        definition: &CompositeResourceDefinition,
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
                Resource::PopulationAuthority(description) => Some(description.clone()),
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
        let next = self.memoized_storage_event(StorageEvent::Control(selected.clone()), || {
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
                opaque_imports: imports,
                ..self.successor()
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
        state: &ExecutionState,
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
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
            (description.arguments()).fixed_values::<1>()
        else {
            return false;
        };
        let Ok(block) = self.exact_member_block(&pointer.address().base, description) else {
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
    ) -> Option<(bool, OldMachineTerm)> {
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
                        OldMachineTerm::constant(u32::from(member.owner.is_some())),
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
                OldMachineTerm::add(
                    import.symbolic_delta.as_ref()?.1.clone(),
                    OldMachineTerm::constant(import.owned_members),
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
                Some((true, OldMachineTerm::constant(1)))
            } else if import.owned_members.checked_add(1) == Some(import.entry_owned_members) {
                Some((false, OldMachineTerm::constant(1)))
            } else {
                Some((
                    import.owned_members >= import.entry_owned_members,
                    OldMachineTerm::constant(
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

    /// The imported population whose function-entry count is `variable`, so
    /// a fact about that count can be spelled `old(count(...))`. One visit
    /// per imported population, which is bounded by the contract's clauses.
    pub(in crate::kernel) fn entry_count_population(
        &self,
        variable: crate::kernel::Variable,
    ) -> Option<&ResourceDescription> {
        self.0
            .opaque_imports
            .iter()
            .find_map(|(description, import)| {
                crate::instrumentation::record_deterministic_work(1);
                matches!(
                    &import.entry_count,
                    Some(OldMachineTerm::Variable(entry)) if *entry == variable
                )
                .then_some(description)
            })
    }

    /// For a total a lock acquired, the program point the lock started from.
    pub(in crate::kernel) fn entry_count_acquired_point(
        &self,
        variable: crate::kernel::Variable,
    ) -> Option<crate::kernel::program_point::ProgramPointId> {
        self.0.opaque_imports.iter().find_map(|(_, import)| {
            crate::instrumentation::record_deterministic_work(1);
            matches!(
                &import.entry_count,
                Some(OldMachineTerm::Variable(entry)) if *entry == variable
            )
            .then_some(import.acquired_at)
            .flatten()
        })
    }

    /// Whether the population whose imported total is `variable` still
    /// counts exactly that total: no member was born or consumed since.
    pub(in crate::kernel) fn imported_total_unchanged(
        &self,
        variable: crate::kernel::Variable,
    ) -> bool {
        let Some(description) = self.entry_count_population(variable) else {
            return false;
        };
        self.observe_symbolic(description).is_some_and(|count| {
            count.delta == 0
                && count.symbolic_delta.is_none()
                && count.entry_count == OldMachineTerm::Variable(variable)
        })
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
        quantity: &OldMachineTerm,
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
            opaque_holders: holders,
            opaque_imports: imports,
            ..self.successor()
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
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
            (description.arguments()).fixed_values::<1>()
        else {
            return false;
        };
        let block = &pointer.address().base;
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
        let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
            pattern.arguments().first()
        else {
            return pattern.clone();
        };
        self.0
            .scopes
            .get(&(pointer.address().base.clone(), pattern.family().to_owned()))
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
        let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
            description.arguments().first()
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
                vec![
                    description
                        .arguments()
                        .get(0)
                        .expect("argument index")
                        .into_native(),
                ]
                .into(),
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
            .get(&(pointer.address().base.clone(), description.family().into()))
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
        block: &'a AddressBase,
        description: &ResourceDescription,
    ) -> Result<&'a AddressBase, CreationRefusal> {
        let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
            description.arguments().first()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if !matches!(pointer.address().offset.view(), OffsetView::Constant(0))
            || &pointer.address().base != block
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
        block: &AddressBase,
        family: &str,
    ) -> Result<u32, CreationRefusal> {
        if *block == AddressBase::ExternalArgument && !self.0.opaque_imports.is_empty() {
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

    /// A fresh entry count for the exact member `member`, registered so a
    /// diagnostic spells it `old(count(R(a, k)))`.
    fn fresh_member_entry_count(member: &ResourceDescription) -> OldMachineTerm {
        let variable =
            crate::kernel::Variable::allocate_fresh().expect("exact count identity exhausted");
        if let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(anchor))) =
            member.arguments().first()
        {
            crate::kernel::model_fields::register_population_entry_count(
                variable,
                crate::kernel::model_fields::PopulationEntryCount {
                    family: Arc::from(member.family()),
                    anchor: anchor.address().clone(),
                    wildcards: 0,
                    member: Some(member.arguments().to_vec().into()),
                },
            );
        }
        OldMachineTerm::Variable(variable)
    }

    /// An exact count is global to the family, not the caller's owned quantity.
    /// Concrete keys need decidable identity; imported keys have arbitrary entry
    /// counts and change only when the checked selected member changes.
    pub(in crate::kernel) fn observe_exact_member(
        &self,
        description: &ResourceDescription,
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
                    .or_insert_with(|| Self::fresh_member_entry_count(description))
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
                    entry_count: OldMachineTerm::constant(u32::from(member.owner.is_some())),
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
            // The member is matched as written: the facts never choose which
            // member's key a count reads.
            let matches = selected.is_some_and(|member| {
                member
                    .arguments()
                    .iter()
                    .zip(description.arguments())
                    .all(|(a, b)| match (a, b) {
                        (
                            crate::kernel::ResourceFieldValue::Program(a),
                            crate::kernel::ResourceFieldValue::Program(b),
                        ) => a.numeric_value() == b.numeric_value(),
                        _ => a == b,
                    })
            });
            // The initial authority-only entry may describe a future birth.
            // Once a member is selected, do not assume another potentially
            // aliased index was unaffected by its exchange.
            if selected.is_some() && !matches {
                return Err(CreationRefusal::InvalidMember);
            }
            let member = selected.filter(|_| matches).unwrap_or(description);
            let key = Self::exact_count_key(member);
            let entry_count = import
                .exact_entry_counts
                .lock()
                .expect("exact entry counts")
                .entry(key)
                .or_insert_with(|| Self::fresh_member_entry_count(member))
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
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(anchor))]) =
            (scope.arguments()).fixed_values::<1>()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if self
            .observed_symbolic_batch(&anchor.address().base, scope.family())
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
            .observe_term(&anchor.address().base, scope.family())?
            .as_const()
            == Some(0);
        if (!Self::has_concrete_indices(description) || unresolved) && !empty {
            return Err(CreationRefusal::InvalidMember);
        }
        Ok(SymbolicPopulationCount {
            entry_count: OldMachineTerm::constant(if empty {
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
            AlgebraicValue::Program(ProgramValue::Pointer(pointer)) => {
                let mut address = pointer.address().clone();
                if let Some(offset) = address.offset.as_const() {
                    address.set_offset(AddressOffset::constant(offset));
                }
                AlgebraicValue::Program(ProgramValue::pointer(address))
            }
            AlgebraicValue::Program(ProgramValue::Int32(value)) => {
                // A read of a stored cell is the index stored there (the
                // read-over-write authority), as the index was when the
                // member was created.
                let value = crate::kernel::read_over_write_value(value).unwrap_or(value.clone());
                AlgebraicValue::Program(ProgramValue::Int32(
                    value
                        .as_const()
                        .map(OldMachineTerm::constant)
                        .unwrap_or(value),
                ))
            }
            other => other.clone(),
        })
    }

    fn has_concrete_indices(description: &ResourceDescription) -> bool {
        description.arguments().iter().all(|value| match value {
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer)) => {
                matches!(pointer.address().base, AddressBase::Heap(_))
                    || pointer.address().base.is_local_block()
            }
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Int32(value)) => {
                value.as_const().is_some()
            }
            _ => false,
        }) && description.arguments().iter().all(|value| match value {
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer)) => {
                pointer.address().offset.as_const().is_some()
            }
            _ => true,
        })
    }

    /// Observe the exact concrete-anchor total, including one outstanding
    /// symbolic batch, only while this holder owns population authority.
    pub(in crate::kernel) fn observe_term(
        &self,
        block: &AddressBase,
        family: &str,
    ) -> Result<OldMachineTerm, CreationRefusal> {
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
        let base = OldMachineTerm::constant(base);
        Ok(match self.0.symbolic_batches.get(&population) {
            Some(batch) => OldMachineTerm::add(base, batch.quantity.clone()),
            None => base,
        })
    }

    pub(in crate::kernel) fn observed_symbolic_batch(
        &self,
        block: &AddressBase,
        family: &str,
    ) -> Option<(u32, OldMachineTerm)> {
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
        block: &AddressBase,
        description: &ResourceDescription,
        produce: bool,
        quantity: &OldMachineTerm,
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
        block: &AddressBase,
        description: &ResourceDescription,
        produce: bool,
        quantity: &OldMachineTerm,
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
            .map(|value| OldMachineTerm::constant(value as u32));
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
            .map(OldMachineTerm::constant);
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
                    assumptions.exact_condition_value(&crate::kernel::OldConditionTerm::equal(
                        entry.clone(),
                        OldMachineTerm::constant(0),
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
                    OldMachineTerm::add(entry, OldMachineTerm::constant(delta as u32))
                } else {
                    OldMachineTerm::subtract(entry, OldMachineTerm::constant((-delta) as u32))
                };
                if !bounded
                    && assumptions.exact_signed_add_overflow(&current, quantity) != Some(false)
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
            crate::kernel::StoredConditionTerm::signed_int32_at_least(
                quantity,
                &OldMachineTerm::constant(0),
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
                let maximum = OldMachineTerm::constant(i32::MAX as u32 - base);
                if !crate::kernel::quantity_condition_holds(
                    assumptions,
                    crate::kernel::StoredConditionTerm::signed_int32_at_least(&maximum, quantity),
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
                symbolic_batches: batches,
                symbolic_holders: holders,
                tainted,
                ..self.successor()
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
                        Some(OldMachineTerm::add(
                            count.entry_count.clone(),
                            count.combined_delta()?.1,
                        ))
                    })
                    .ok_or(CreationRefusal::MissingAuthority)?;
                if assumptions.exact_signed_add_overflow(&current, quantity) != Some(false) {
                    return Err(CreationRefusal::InvalidQuantity);
                }
                Some((true, OldMachineTerm::add(prior.clone(), quantity.clone())))
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
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
            (description.arguments()).fixed_values::<1>()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if &pointer.address().base != block {
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
            opaque_holders: self.adjust_opaque_right(
                self.0.opaque_actor,
                import.entry_symbolic_members.is_some() || import.symbolic_delta.is_some(),
                produce,
            ),
            opaque_imports: self.0.opaque_imports.with_inserted(
                description.clone(),
                OpaqueImport {
                    symbolic_delta,
                    symbolic_member_holder: produce.then_some(self.0.opaque_actor),
                    ..import.clone()
                },
            ),
            ..self.successor()
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
        block: &AddressBase,
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
        let key = StorageEvent::InstanceMember(reference.clone(), produce);
        if let Some(existing) = self
            .0
            .storage_events
            .lock()
            .expect("C event cache")
            .get(&key)
        {
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
                OldMachineTerm::add(
                    entry.clone(),
                    OldMachineTerm::constant(aggregate.delta as u32),
                )
            } else {
                OldMachineTerm::subtract(
                    entry.clone(),
                    OldMachineTerm::constant(aggregate.delta.unsigned_abs()),
                )
            };
            if assumptions.exact_signed_add_overflow(&current, &OldMachineTerm::constant(1))
                != Some(false)
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
            !matches!(value, crate::kernel::ResourceFieldValue::Program(ProgramValue::Int32(value)) if value.as_const().is_some())
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
            opaque_imports: self.0.opaque_imports.with_inserted(
                scope.clone(),
                OpaqueImport {
                    symbolic_delta: (aggregate.delta != 0).then(|| {
                        (
                            aggregate.delta > 0,
                            OldMachineTerm::constant(aggregate.delta.unsigned_abs()),
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
            ..self.successor()
        }));
        Ok(self
            .0
            .storage_events
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
        identity: crate::kernel::InstanceId,
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
        let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
            description.arguments().first()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if description.population_arity().is_some()
            || !description.resource_arguments().is_empty()
            || self.recognizes_imported_population(description)
        {
            return Err(CreationRefusal::InvalidMember);
        }
        let key = StorageEvent::InstanceMember(reference.clone(), produce);
        if let Some(existing) = self
            .0
            .storage_events
            .lock()
            .expect("C event cache")
            .get(&key)
        {
            return Ok(existing.clone());
        }
        let (next, _) = self.checked_member_exchange_with_context(
            &pointer.address().base,
            description,
            produce,
            None,
            1,
            MemberForm::Instance,
        )?;
        Ok(self
            .0
            .storage_events
            .lock()
            .expect("C event cache")
            .entry(key)
            .or_insert(next)
            .clone())
    }

    fn checked_member_exchange_with_context(
        &self,
        block: &AddressBase,
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
                        OldMachineTerm::add(entry.clone(), OldMachineTerm::constant(delta as u32))
                    } else {
                        OldMachineTerm::subtract(
                            entry.clone(),
                            OldMachineTerm::constant((-delta) as u32),
                        )
                    };
                    if !assumptions.is_some_and(|facts| {
                        facts.exact_signed_add_overflow(&total, &OldMachineTerm::constant(1))
                            == Some(false)
                            || facts
                                .equality_graph
                                .signed_int32_interval(&entry)
                                .is_some_and(|(_, high)| high + delta < i64::from(i32::MAX))
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
                            Some(OldMachineTerm::add(
                                count.entry_count.clone(),
                                count.combined_delta()?.1,
                            ))
                        })
                        .ok_or(CreationRefusal::MissingAuthority)?;
                    let amount_word = OldMachineTerm::constant(amount);
                    if !assumptions.is_some_and(|facts| {
                        facts.exact_signed_add_overflow(&current, &amount_word) == Some(false)
                            || facts
                                .indexed_constant_interval(&current)
                                .is_some_and(|(_, high)| {
                                    high + i64::from(amount) <= i64::from(i32::MAX)
                                })
                            || PureFactContext::decide_intrinsically(
                                &crate::kernel::OldConditionTerm::signed_add_overflows(
                                    current.clone(),
                                    amount_word,
                                ),
                            ) == Some(false)
                    }) {
                        return Err(CreationRefusal::InvalidQuantity);
                    }
                }
            }
            // Opaque custody follows only checked exact contract transfers;
            // numeric exchanges change the global fragment total separately.
            let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
                description.arguments().first()
            else {
                return Err(CreationRefusal::InvalidMember);
            };
            if &pointer.address().base != block {
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
                opaque_holders: self.adjust_opaque_right(
                    self.0.opaque_actor,
                    held > 0,
                    next_held > 0,
                ),
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
                ..self.successor()
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
            authority,
            tainted,
            exact_members,
            ..self.successor()
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
            storage_events: Mutex::new(BTreeMap::new()),
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
                    invocation: Holder::fresh(),
                    opaque_actor: Holder::fresh(),
                    ..self.successor()
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
                    invocation: Holder::fresh(),
                    ..self.successor()
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
            &OldMachineTerm::constant(1),
            &PureFactContext::new(),
        )
    }

    pub(in crate::kernel) fn transfer_call_fact_quantity(
        &self,
        from: &Self,
        to: &Self,
        description: &ResourceDescription,
        authority_fact: bool,
        quantity: &OldMachineTerm,
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
            .map(OldMachineTerm::constant);
        let quantity = numerical.as_ref().unwrap_or(quantity);
        // Zero ownership transports no member capability, including when a
        // checked contract equality establishes that a field-valued quantity
        // is zero. It cannot move the authority or justify a unit operation.
        if !authority_fact && same_quantity(quantity, &OldMachineTerm::constant(0), assumptions) {
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
        let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
            description.arguments().first()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        let block = self.exact_member_block(&pointer.address().base, description)?;
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
            authority,
            symbolic_batches: batches,
            symbolic_holders: holders,
            ..self.successor()
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
    pub(in crate::kernel) fn tracks_storage_anchor(&self, block: &AddressBase) -> bool {
        self.0.anchors.contains_key(block)
    }

    pub(in crate::kernel) fn transfer_call_anchor(
        &self,
        from: &Self,
        to: &Self,
        block: &AddressBase,
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
        Ok(self.memoized_storage_event(
            StorageEvent::TransferredAnchor(from.0.invocation, to.0.invocation, block.clone()),
            || {
                Self(Arc::new(Root {
                    authority,
                    ..self.successor()
                }))
            },
        ))
    }

    pub(in crate::kernel) fn tracks_population(&self, description: &ResourceDescription) -> bool {
        if self.recognizes_imported_population(description) {
            return true;
        }
        let Some(crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))) =
            description.arguments().first()
        else {
            return false;
        };
        if self.governing_authority(description).is_none() {
            return false;
        }
        self.0
            .anchors
            .get(&pointer.address().base)
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
            invocation: caller.0.invocation,
            opaque_actor: caller.0.opaque_actor,
            ..self.successor()
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
    pub(in crate::kernel) fn pending_creation(&self, block: AddressBase) -> Self {
        self.memoized_storage_event(StorageEvent::Pending(block.clone()), || {
            self.pending_creation_uncached(block)
        })
    }

    fn pending_creation_uncached(&self, block: AddressBase) -> Self {
        debug_assert!(matches!(&block, AddressBase::Symbolic(_)));
        assert!(
            !self.0.pending.contains_key(&block),
            "pending allocation reused"
        );
        let mut pending = self.0.pending.clone();
        pending.insert(block, self.0.invocation);
        Self(Arc::new(Root {
            pending,
            ..self.successor()
        }))
    }

    /// Resolve an actual pending allocation. Failure discards its origin;
    /// success attaches the original creator to the trusted Heap block even
    /// when a helper made the deciding branch.
    pub(in crate::kernel) fn resolve_pending(
        &self,
        pending_block: &AddressBase,
        live_block: Option<AddressBase>,
    ) -> Self {
        self.memoized_storage_event(
            StorageEvent::Resolve(pending_block.clone(), live_block.clone()),
            || self.resolve_pending_uncached(pending_block, live_block),
        )
    }

    fn resolve_pending_uncached(
        &self,
        pending_block: &AddressBase,
        live_block: Option<AddressBase>,
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
            debug_assert!(matches!(&block, AddressBase::Heap(_)));
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
            pending,
            creators,
            anchors,
            authority,
            tainted,
            empty_populations,
            ..self.successor()
        }))
    }

    /// Called only at checked C storage creation, never at resource lowering,
    /// contract allocation import, or generic memory-block construction.
    pub(in crate::kernel) fn created(&self, block: AddressBase) -> Self {
        self.memoized_storage_event(StorageEvent::Created(block.clone()), || {
            self.created_uncached(block)
        })
    }

    fn created_uncached(&self, block: AddressBase) -> Self {
        debug_assert!(matches!(block, AddressBase::Heap(_)) || block.is_local_block());
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
            creators,
            anchors,
            authority,
            empty_populations: self.0.empty_populations.without_key(&block),
            ..self.successor()
        }))
    }

    /// Query the allocator's recorded creator for one selected storage block.
    /// Call entry retains its creator scope, so returns never search aliases
    /// or compare growing event histories to recover allocation freshness.
    pub(in crate::kernel) fn storage_created_by(&self, scope: &Self, block: &AddressBase) -> bool {
        crate::instrumentation::record_deterministic_work(1);
        self.0.creators.get(block).copied() == Some(scope.0.invocation)
    }

    pub(in crate::kernel) fn same_invocation(&self, other: &Self) -> bool {
        self.0.invocation == other.0.invocation
    }

    pub(in crate::kernel) fn created_here(&self, block: &AddressBase) -> bool {
        self.0.creators.get(block).copied() == Some(self.0.invocation)
    }

    pub(in crate::kernel) fn retirement_refusal(
        &self,
        block: &AddressBase,
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
    pub(in crate::kernel) fn member_created(&self, block: &AddressBase, family: &str) -> Self {
        if !self.0.creators.contains_key(block) && !self.0.pending.contains_key(block) {
            return self.clone();
        }
        self.memoized_storage_event(
            StorageEvent::MemberCreated(block.clone(), family.to_owned()),
            || self.member_created_uncached(block, family),
        )
    }

    fn member_created_uncached(&self, block: &AddressBase, family: &str) -> Self {
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
            tainted,
            ..self.successor()
        }))
    }

    #[cfg(test)]
    /// A checked source fold may establish only at its own creation event,
    /// before any member of this family has existed in the storage lifetime.
    pub(in crate::kernel) fn establish(
        &self,
        block: &AddressBase,
        family: &str,
    ) -> Result<Self, CreationRefusal> {
        self.establish_scoped(block, family, None)
    }

    fn establish_scoped(
        &self,
        block: &AddressBase,
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
            authority,
            scopes: match scope {
                Some(scope) => self
                    .0
                    .scopes
                    .with_inserted((block.clone(), family.into()), scope.clone()),
                None => self.0.scopes.clone(),
            },
            ..self.successor()
        })))
    }

    pub(in crate::kernel) fn checked_establish(
        &self,
        block: &AddressBase,
        description: &ResourceDescription,
    ) -> Result<(Self, CheckedPopulationAuthorityExchange), CreationRefusal> {
        let Some([crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(pointer))]) =
            (description.arguments()).fixed_values::<1>()
        else {
            return Err(CreationRefusal::InvalidMember);
        };
        if &pointer.address().base != block
            || !matches!(pointer.address().offset.view(), OffsetView::Constant(0))
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
        block: &AddressBase,
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
            .unwrap_or(OldMachineTerm::constant(symbolic.delta.unsigned_abs()));
        let current = OldMachineTerm::subtract(symbolic.entry_count.clone(), consumed.clone());
        if !same_quantity(&symbolic.entry_count, &consumed, assumptions)
            && !same_quantity(&current, &OldMachineTerm::constant(0), assumptions)
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
            opaque_holders: self.adjust_opaque_right(self.0.opaque_actor, true, false),
            opaque_imports: self.0.opaque_imports.with_inserted(
                description.clone(),
                OpaqueImport {
                    retired_authority: true,
                    ..import.clone()
                },
            ),
            ..self.successor()
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
        block: &AddressBase,
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
            authority,
            empty_populations: self.0.empty_populations.with_inserted(
                block.clone(),
                self.0
                    .empty_populations
                    .get(block)
                    .cloned()
                    .unwrap_or_default()
                    .with_value(family.to_owned()),
            ),
            ..self.successor()
        })))
    }

    /// End of an automatic or heap lifetime removes its creation record. Future
    /// reuse at the same address needs an independently checked creation.
    pub(in crate::kernel) fn retired(&self, block: &AddressBase) -> Result<Self, CreationRefusal> {
        if !self.0.creators.contains_key(block) {
            return Ok(self.clone());
        }
        if let Some(refusal) = self.retirement_refusal(block) {
            return Err(refusal);
        }
        Ok(
            self.memoized_storage_event(StorageEvent::Retired(block.clone()), || {
                self.retired_uncached(block)
                    .expect("retirement was checked before memoizing")
            }),
        )
    }

    fn retired_uncached(&self, block: &AddressBase) -> Result<Self, CreationRefusal> {
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
            creators,
            anchors,
            authority,
            tainted: self.0.tainted.without_key(block),
            ..self.successor()
        })))
    }
}

#[cfg(test)]
mod tests;
