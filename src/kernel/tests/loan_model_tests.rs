//! Executable design model for stable shared loans.
//!
//! This is deliberately independent of the production loan ledger. It fixes
//! the conservation laws and cross-context counterexamples before the kernel
//! representation is used by C contract transfer.
//!
//! V14 design handoff: the extension model treats a context as an abstract
//! sequential actor and explores interleavings only at explicit transition
//! boundaries. Memory is a bounded array of initialized byte cells; ranges
//! are nonempty, concrete, and at most eight cells wide in the witnesses.
//! The original loan search remains depth five with a 50,000-state cap, and
//! extension identities are eight-bit counters with checked exhaustion. This
//! is not a release/acquire, allocator, or C data-race proof: atomics,
//! scheduling fairness, cache visibility, C lifetime races, Rust trait/unsafe
//! alias rules, and production thread APIs are intentionally omitted.
//!
//! Shared model steps correspond to the checked kernel `lend`, `split`,
//! `transfer`, `join`, `end`, `recover`, planner partition, and shared
//! `reborrow` operations exercised below. Exclusive reborrow, returned-value
//! transport, mutex invariant/guard transitions, and thread-local mutable
//! cells are model-only extension operations; they have no production API.
//! Their preservation arguments are local: partition replaces one owned range
//! by disjoint residuals; lending removes that range from usable ownership;
//! splitting creates both conserved children and joining consumes both exact
//! siblings; transfer changes only a holder; ending requires the reconstructed
//! root; recovery restores the escrow once; shared reborrow pins its parent
//! until child closure; exclusive reborrow suspends all parent access and
//! returns the child value before restoring the parent field; mutex release
//! restores its invariant; and a local cell accepts access only at its home
//! context. Model invariants are checked independently and never delegated to
//! production validity helpers.

use std::collections::{BTreeMap, BTreeSet};

use crate::kernel::functions::CCheckedResourceFact;
use crate::kernel::loans::{LoanLedger, LoanRefusal, LoanViewBinding, plan_stable_view_transfer};
use crate::kernel::{
    Bitvector32Term, CMemoryRange, CResourceFact, CResourceSnapshot, CResourceTransferRole,
    Pointer, PointerOffsetTerm, PureFactContext, ResourceContext, ResourceOccurrenceId,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum Holder {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Location(u8);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ScopeId(u16);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct LoanId(u16);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ShareId(u16);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ViewDescription {
    loan: LoanId,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Scope {
    active: bool,
    root: ShareId,
    close_holder: Holder,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Loan {
    scope: ScopeId,
    location: Location,
    recovery_holder: Holder,
    recovered: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Share {
    scope: ScopeId,
    parent: Option<ShareId>,
    children: Option<(ShareId, ShareId)>,
    active_holder: Option<Holder>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct Model {
    owners: BTreeMap<Location, Holder>,
    values: BTreeMap<Location, u8>,
    scopes: BTreeMap<ScopeId, Scope>,
    loans: BTreeMap<LoanId, Loan>,
    shares: BTreeMap<ShareId, Share>,
    next_scope: u16,
    next_loan: u16,
    next_share: u16,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Refusal {
    MissingOwner,
    MissingShare,
    WrongHolder,
    WrongScope,
    ScopeEnded,
    ScopeStillActive,
    ShareStillSplit,
    NotSiblings,
    MissingCloseRight,
    AlreadyRecovered,
}

impl Model {
    fn with_owned(locations: impl IntoIterator<Item = (Location, Holder, u8)>) -> Self {
        let mut model = Self {
            owners: BTreeMap::new(),
            values: BTreeMap::new(),
            scopes: BTreeMap::new(),
            loans: BTreeMap::new(),
            shares: BTreeMap::new(),
            next_scope: 0,
            next_loan: 0,
            next_share: 0,
        };
        for (location, holder, value) in locations {
            assert!(model.owners.insert(location, holder).is_none());
            assert!(model.values.insert(location, value).is_none());
        }
        model
    }

    fn fresh_share(&mut self) -> ShareId {
        let share = ShareId(self.next_share);
        self.next_share = self
            .next_share
            .checked_add(1)
            .expect("small model share ids");
        share
    }

    fn lend(
        &mut self,
        owner: Holder,
        reader: Holder,
        location: Location,
    ) -> Result<(ScopeId, LoanId, ShareId, ViewDescription), Refusal> {
        if self.owners.get(&location) != Some(&owner) {
            return Err(Refusal::MissingOwner);
        }
        self.owners.remove(&location);
        let scope = ScopeId(self.next_scope);
        self.next_scope += 1;
        let loan = LoanId(self.next_loan);
        self.next_loan += 1;
        let root = self.fresh_share();
        self.scopes.insert(
            scope,
            Scope {
                active: true,
                root,
                close_holder: owner,
            },
        );
        self.loans.insert(
            loan,
            Loan {
                scope,
                location,
                recovery_holder: owner,
                recovered: false,
            },
        );
        self.shares.insert(
            root,
            Share {
                scope,
                parent: None,
                children: None,
                active_holder: Some(reader),
            },
        );
        Ok((scope, loan, root, ViewDescription { loan }))
    }

    fn split(
        &mut self,
        share: ShareId,
        holder: Holder,
        left_holder: Holder,
        right_holder: Holder,
    ) -> Result<(ShareId, ShareId), Refusal> {
        let available = self.shares.get(&share).ok_or(Refusal::MissingShare)?;
        if available.active_holder != Some(holder) {
            return Err(Refusal::WrongHolder);
        }
        let scope = available.scope;
        if !self.scopes.get(&scope).is_some_and(|scope| scope.active) {
            return Err(Refusal::ScopeEnded);
        }
        let left = self.fresh_share();
        let right = self.fresh_share();
        let parent = self.shares.get_mut(&share).expect("checked above");
        parent.active_holder = None;
        parent.children = Some((left, right));
        self.shares.insert(
            left,
            Share {
                scope,
                parent: Some(share),
                children: None,
                active_holder: Some(left_holder),
            },
        );
        self.shares.insert(
            right,
            Share {
                scope,
                parent: Some(share),
                children: None,
                active_holder: Some(right_holder),
            },
        );
        Ok((left, right))
    }

    fn transfer(&mut self, share: ShareId, from: Holder, to: Holder) -> Result<(), Refusal> {
        let share = self.shares.get_mut(&share).ok_or(Refusal::MissingShare)?;
        if share.active_holder != Some(from) {
            return Err(Refusal::WrongHolder);
        }
        share.active_holder = Some(to);
        Ok(())
    }

    fn join(&mut self, left: ShareId, right: ShareId, holder: Holder) -> Result<ShareId, Refusal> {
        let left_share = self.shares.get(&left).ok_or(Refusal::MissingShare)?;
        let right_share = self.shares.get(&right).ok_or(Refusal::MissingShare)?;
        if left_share.active_holder != Some(holder) || right_share.active_holder != Some(holder) {
            return Err(Refusal::WrongHolder);
        }
        if left_share.scope != right_share.scope {
            return Err(Refusal::WrongScope);
        }
        let Some(parent) = left_share.parent else {
            return Err(Refusal::NotSiblings);
        };
        if right_share.parent != Some(parent)
            || self.shares.get(&parent).and_then(|share| share.children) != Some((left, right))
        {
            return Err(Refusal::NotSiblings);
        }
        self.shares.get_mut(&left).expect("checked").active_holder = None;
        self.shares.get_mut(&right).expect("checked").active_holder = None;
        self.shares.get_mut(&parent).expect("checked").active_holder = Some(holder);
        Ok(parent)
    }

    fn read(
        &self,
        holder: Holder,
        description: ViewDescription,
        share: ShareId,
    ) -> Result<u8, Refusal> {
        let loan = self
            .loans
            .get(&description.loan)
            .ok_or(Refusal::WrongScope)?;
        let scope = self.scopes.get(&loan.scope).ok_or(Refusal::WrongScope)?;
        if !scope.active {
            return Err(Refusal::ScopeEnded);
        }
        let share = self.shares.get(&share).ok_or(Refusal::MissingShare)?;
        if share.scope != loan.scope {
            return Err(Refusal::WrongScope);
        }
        if share.active_holder != Some(holder) {
            return Err(Refusal::WrongHolder);
        }
        Ok(*self
            .values
            .get(&loan.location)
            .expect("loaned location is live"))
    }

    fn write(&mut self, holder: Holder, location: Location, value: u8) -> Result<(), Refusal> {
        if self.owners.get(&location) != Some(&holder) {
            return Err(Refusal::MissingOwner);
        }
        self.values.insert(location, value);
        Ok(())
    }

    fn end(&mut self, holder: Holder, scope: ScopeId) -> Result<(), Refusal> {
        let scope_record = self.scopes.get(&scope).ok_or(Refusal::WrongScope)?;
        if !scope_record.active {
            return Err(Refusal::ScopeEnded);
        }
        if scope_record.close_holder != holder {
            return Err(Refusal::MissingCloseRight);
        }
        let root = self
            .shares
            .get(&scope_record.root)
            .ok_or(Refusal::MissingShare)?;
        if root.active_holder != Some(holder) {
            return Err(Refusal::ShareStillSplit);
        }
        self.shares
            .get_mut(&scope_record.root)
            .expect("checked")
            .active_holder = None;
        self.scopes.get_mut(&scope).expect("checked").active = false;
        Ok(())
    }

    fn recover(&mut self, holder: Holder, loan: LoanId) -> Result<(), Refusal> {
        let loan_record = self.loans.get(&loan).ok_or(Refusal::WrongScope)?;
        if loan_record.recovery_holder != holder {
            return Err(Refusal::WrongHolder);
        }
        if loan_record.recovered {
            return Err(Refusal::AlreadyRecovered);
        }
        if self
            .scopes
            .get(&loan_record.scope)
            .is_some_and(|scope| scope.active)
        {
            return Err(Refusal::ScopeStillActive);
        }
        let location = loan_record.location;
        self.loans.get_mut(&loan).expect("checked").recovered = true;
        assert!(self.owners.insert(location, holder).is_none());
        Ok(())
    }

    fn invariant_holds(&self) -> bool {
        for location in self.values.keys() {
            let live_escrows = self
                .loans
                .values()
                .filter(|loan| loan.location == *location && !loan.recovered)
                .count();
            if live_escrows > 1 || self.owners.contains_key(location) == (live_escrows == 1) {
                return false;
            }
        }
        for (loan_id, loan) in &self.loans {
            let Some(scope) = self.scopes.get(&loan.scope) else {
                return false;
            };
            if loan.recovered && scope.active {
                return false;
            }
            if !self.scope_tree_is_conserved(loan.scope, scope.root) {
                return false;
            }
            if !loan.recovered
                && self.loans.iter().any(|(other_id, other)| {
                    other_id != loan_id && !other.recovered && other.location == loan.location
                })
            {
                return false;
            }
        }
        self.scopes.iter().all(|(scope_id, scope)| {
            scope.active
                == self
                    .shares
                    .values()
                    .any(|share| share.scope == *scope_id && share.active_holder.is_some())
        })
    }

    fn scope_tree_is_conserved(&self, scope: ScopeId, share: ShareId) -> bool {
        let Some(record) = self.shares.get(&share) else {
            return false;
        };
        if record.scope != scope {
            return false;
        }
        if record.active_holder.is_some() {
            return !self.descendant_is_active(record);
        }
        match record.children {
            Some((left, right)) => {
                self.scope_tree_is_conserved(scope, left)
                    && self.scope_tree_is_conserved(scope, right)
            }
            None => !self.scopes.get(&scope).is_some_and(|scope| scope.active),
        }
    }

    fn descendant_is_active(&self, record: &Share) -> bool {
        let Some((left, right)) = record.children else {
            return false;
        };
        [left, right].into_iter().any(|child| {
            let child = self
                .shares
                .get(&child)
                .expect("share children are retained");
            child.active_holder.is_some() || self.descendant_is_active(child)
        })
    }
}

#[test]
fn two_reader_trace_conserves_authority_and_rejects_stale_description() {
    let x = Location(0);
    let mut model = Model::with_owned([(x, Holder::Left, 0)]);
    let (scope, loan, root, view) = model.lend(Holder::Left, Holder::Left, x).unwrap();
    let copied_view = view;
    let (left, right) = model
        .split(root, Holder::Left, Holder::Left, Holder::Right)
        .unwrap();
    assert_eq!(model.read(Holder::Left, view, left), Ok(0));
    assert_eq!(model.read(Holder::Right, copied_view, right), Ok(0));
    assert_eq!(model.write(Holder::Left, x, 0), Err(Refusal::MissingOwner));
    assert_eq!(
        model.end(Holder::Left, scope),
        Err(Refusal::ShareStillSplit)
    );
    model.transfer(right, Holder::Right, Holder::Left).unwrap();
    assert_eq!(model.join(left, right, Holder::Left), Ok(root));
    model.end(Holder::Left, scope).unwrap();
    model.recover(Holder::Left, loan).unwrap();
    model.write(Holder::Left, x, 1).unwrap();
    assert_eq!(
        model.read(Holder::Left, copied_view, root),
        Err(Refusal::ScopeEnded)
    );
    assert_eq!(
        model.recover(Holder::Left, loan),
        Err(Refusal::AlreadyRecovered)
    );
    let (_new_scope, _new_loan, _new_root, _new_view) =
        model.lend(Holder::Left, Holder::Left, x).unwrap();
    assert_eq!(
        model.read(Holder::Left, copied_view, root),
        Err(Refusal::ScopeEnded)
    );
    assert!(model.invariant_holds());
}

#[test]
fn splitting_and_joining_require_exact_linear_siblings() {
    let x = Location(0);
    let mut model = Model::with_owned([(x, Holder::Left, 3)]);
    let (scope, _loan, root, _view) = model.lend(Holder::Left, Holder::Left, x).unwrap();
    let (left, right) = model
        .split(root, Holder::Left, Holder::Left, Holder::Left)
        .unwrap();
    assert_eq!(
        model.split(root, Holder::Left, Holder::Left, Holder::Left),
        Err(Refusal::WrongHolder)
    );
    assert_eq!(
        model.join(left, left, Holder::Left),
        Err(Refusal::NotSiblings)
    );
    model.transfer(right, Holder::Left, Holder::Right).unwrap();
    assert_eq!(
        model.join(left, right, Holder::Left),
        Err(Refusal::WrongHolder)
    );
    assert_eq!(
        model.end(Holder::Left, scope),
        Err(Refusal::ShareStillSplit)
    );
    assert!(model.invariant_holds());
}

#[test]
fn lending_is_frame_preserving_for_an_unrelated_owner() {
    let x = Location(0);
    let y = Location(1);
    let mut framed = Model::with_owned([(x, Holder::Left, 7), (y, Holder::Right, 9)]);
    let (_, _, root, view) = framed.lend(Holder::Left, Holder::Right, x).unwrap();
    assert_eq!(framed.read(Holder::Right, view, root), Ok(7));
    framed.write(Holder::Right, y, 10).unwrap();
    assert_eq!(framed.values.get(&y), Some(&10));
    assert_eq!(framed.owners.get(&y), Some(&Holder::Right));
    assert!(framed.invariant_holds());
}

#[test]
fn owner_plus_independent_view_is_the_rejected_naive_model() {
    #[derive(Clone, Copy)]
    struct NaiveCell {
        owner_can_write: bool,
        independent_view_can_read: bool,
    }
    fn stable_view_invariant(cell: NaiveCell) -> bool {
        !(cell.owner_can_write && cell.independent_view_can_read)
    }
    assert!(!stable_view_invariant(NaiveCell {
        owner_can_write: true,
        independent_view_can_read: true,
    }));
}

fn bounded_successors(model: &Model) -> Vec<Model> {
    let mut successors = BTreeSet::new();
    for holder in [Holder::Left, Holder::Right] {
        for location in [Location(0), Location(1)] {
            for reader in [Holder::Left, Holder::Right] {
                let mut next = model.clone();
                if next.lend(holder, reader, location).is_ok() {
                    successors.insert(next);
                }
            }
            let mut next = model.clone();
            if next.write(holder, location, 1).is_ok() {
                successors.insert(next);
            }
        }
    }
    for share in model.shares.keys().copied() {
        for holder in [Holder::Left, Holder::Right] {
            let mut next = model.clone();
            if next
                .split(share, holder, Holder::Left, Holder::Right)
                .is_ok()
            {
                successors.insert(next);
            }
            let mut next = model.clone();
            let other = match holder {
                Holder::Left => Holder::Right,
                Holder::Right => Holder::Left,
            };
            if next.transfer(share, holder, other).is_ok() {
                successors.insert(next);
            }
        }
    }
    let share_ids = model.shares.keys().copied().collect::<Vec<_>>();
    for (index, left) in share_ids.iter().enumerate() {
        for right in &share_ids[index..] {
            for holder in [Holder::Left, Holder::Right] {
                let mut next = model.clone();
                if next.join(*left, *right, holder).is_ok() {
                    successors.insert(next);
                }
            }
        }
    }
    for scope in model.scopes.keys().copied() {
        for holder in [Holder::Left, Holder::Right] {
            let mut next = model.clone();
            if next.end(holder, scope).is_ok() {
                successors.insert(next);
            }
        }
    }
    for loan in model.loans.keys().copied() {
        for holder in [Holder::Left, Holder::Right] {
            let mut next = model.clone();
            if next.recover(holder, loan).is_ok() {
                successors.insert(next);
            }
        }
    }
    successors.into_iter().collect()
}

#[test]
fn bounded_reachable_states_preserve_the_model_invariant() {
    const DEPTH: usize = 5;
    const MAX_STATES: usize = 50_000;
    let initial = Model::with_owned([
        (Location(0), Holder::Left, 0),
        (Location(1), Holder::Right, 0),
    ]);
    let mut frontier = BTreeSet::from([initial]);
    let mut visited = BTreeSet::new();
    for _ in 0..=DEPTH {
        let mut next = BTreeSet::new();
        for state in frontier {
            assert!(
                state.invariant_holds(),
                "invalid reachable state: {state:#?}"
            );
            if !visited.insert(state.clone()) {
                continue;
            }
            assert!(
                visited.len() <= MAX_STATES,
                "bounded model exceeded its stated limit"
            );
            next.extend(bounded_successors(&state));
        }
        frontier = next;
    }
    assert!(visited.len() > 100, "model enumeration was not meaningful");
}

// The following types are deliberately a second, extension-only model.  They
// use small context and byte-range identities so that a context split is an
// explicit operation in the model rather than an accidental consequence of
// cloning a proof state.  None of their invariants call production ledger
// validity helpers.

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ContextId(u8);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct ByteRange {
    start: u8,
    end: u8,
}

impl ByteRange {
    fn new(start: u8, end: u8) -> Self {
        assert!(start < end, "model ranges are nonempty and bounded");
        Self { start, end }
    }

    fn overlaps(self, other: Self) -> bool {
        self.start < other.end && other.start < self.end
    }

    fn split(self, at: u8) -> Option<(Self, Self)> {
        (self.start < at && at < self.end)
            .then(|| (Self::new(self.start, at), Self::new(at, self.end)))
    }

    fn join(self, other: Self) -> Option<Self> {
        (self.end == other.start).then(|| Self::new(self.start, other.end))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RangeRefusal {
    MissingOwner,
    Overlap,
    WrongContext,
    MissingShare,
    WrongHolder,
    ScopeEnded,
    ShareStillSplit,
    NotSiblings,
    ScopeStillActive,
    AlreadyRecovered,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct RangeShare {
    range: ByteRange,
    parent: Option<u8>,
    children: Option<(u8, u8)>,
    holder: Option<ContextId>,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct RangeLoan {
    range: ByteRange,
    lender: ContextId,
    active: bool,
    recovered: bool,
    root: u8,
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
struct RangeOwnershipModel {
    values: BTreeMap<u8, u8>,
    owners: BTreeMap<ByteRange, ContextId>,
    loans: BTreeMap<u8, RangeLoan>,
    shares: BTreeMap<u8, RangeShare>,
    next_loan: u8,
    next_share: u8,
}

impl RangeOwnershipModel {
    fn new(values: impl IntoIterator<Item = (ByteRange, ContextId, u8)>) -> Self {
        let mut model = Self {
            values: BTreeMap::new(),
            owners: BTreeMap::new(),
            loans: BTreeMap::new(),
            shares: BTreeMap::new(),
            next_loan: 0,
            next_share: 0,
        };
        for (range, context, value) in values {
            assert!(
                model
                    .owners
                    .keys()
                    .all(|existing| !existing.overlaps(range))
            );
            for byte in range.start..range.end {
                assert!(model.values.insert(byte, value).is_none());
            }
            assert!(model.owners.insert(range, context).is_none());
        }
        model
    }

    fn partition(
        &mut self,
        context: ContextId,
        range: ByteRange,
        at: u8,
    ) -> Result<(ByteRange, ByteRange), RangeRefusal> {
        if self.owners.get(&range) != Some(&context) {
            return Err(RangeRefusal::MissingOwner);
        }
        let (left, right) = range.split(at).ok_or(RangeRefusal::Overlap)?;
        self.owners.remove(&range);
        self.owners.insert(left, context);
        self.owners.insert(right, context);
        Ok((left, right))
    }

    fn transfer(
        &mut self,
        range: ByteRange,
        from: ContextId,
        to: ContextId,
    ) -> Result<(), RangeRefusal> {
        if self.owners.get(&range) != Some(&from) {
            return Err(RangeRefusal::WrongContext);
        }
        self.owners.insert(range, to);
        Ok(())
    }

    fn join(
        &mut self,
        left: ByteRange,
        right: ByteRange,
        context: ContextId,
    ) -> Result<ByteRange, RangeRefusal> {
        if self.owners.get(&left) != Some(&context) || self.owners.get(&right) != Some(&context) {
            return Err(RangeRefusal::WrongContext);
        }
        let joined = left.join(right).ok_or(RangeRefusal::NotSiblings)?;
        self.owners.remove(&left);
        self.owners.remove(&right);
        self.owners.insert(joined, context);
        Ok(joined)
    }

    fn write(
        &mut self,
        context: ContextId,
        range: ByteRange,
        value: u8,
    ) -> Result<(), RangeRefusal> {
        if self.owners.get(&range) != Some(&context) {
            return Err(RangeRefusal::MissingOwner);
        }
        for byte in range.start..range.end {
            self.values.insert(byte, value);
        }
        Ok(())
    }

    fn lend_shared(
        &mut self,
        lender: ContextId,
        reader: ContextId,
        range: ByteRange,
    ) -> Result<(u8, u8), RangeRefusal> {
        if self.owners.get(&range) != Some(&lender) {
            return Err(RangeRefusal::MissingOwner);
        }
        self.owners.remove(&range);
        let loan = self.next_loan;
        self.next_loan = self.next_loan.checked_add(1).expect("tiny loan bound");
        let root = self.next_share;
        self.next_share = self.next_share.checked_add(1).expect("tiny share bound");
        self.loans.insert(
            loan,
            RangeLoan {
                range,
                lender,
                active: true,
                recovered: false,
                root,
            },
        );
        self.shares.insert(
            root,
            RangeShare {
                range,
                parent: None,
                children: None,
                holder: Some(reader),
            },
        );
        Ok((loan, root))
    }

    fn split_share(
        &mut self,
        share: u8,
        holder: ContextId,
        left_holder: ContextId,
        right_holder: ContextId,
    ) -> Result<(u8, u8), RangeRefusal> {
        let parent = self.shares.get(&share).ok_or(RangeRefusal::MissingShare)?;
        if parent.holder != Some(holder) || parent.children.is_some() {
            return Err(RangeRefusal::WrongHolder);
        }
        let left = self.next_share;
        let right = self.next_share.checked_add(1).expect("tiny share bound");
        self.next_share = right.checked_add(1).expect("tiny share bound");
        let range = parent.range;
        let parent = self.shares.get_mut(&share).expect("checked parent");
        parent.holder = None;
        parent.children = Some((left, right));
        for (id, child_holder) in [(left, left_holder), (right, right_holder)] {
            self.shares.insert(
                id,
                RangeShare {
                    range,
                    parent: Some(share),
                    children: None,
                    holder: Some(child_holder),
                },
            );
        }
        Ok((left, right))
    }

    fn transfer_share(
        &mut self,
        share: u8,
        from: ContextId,
        to: ContextId,
    ) -> Result<(), RangeRefusal> {
        let share = self
            .shares
            .get_mut(&share)
            .ok_or(RangeRefusal::MissingShare)?;
        if share.holder != Some(from) {
            return Err(RangeRefusal::WrongHolder);
        }
        share.holder = Some(to);
        Ok(())
    }

    fn read_shared(&self, share: u8, context: ContextId) -> Result<u8, RangeRefusal> {
        let share = self.shares.get(&share).ok_or(RangeRefusal::MissingShare)?;
        if share.holder != Some(context) {
            return Err(RangeRefusal::WrongHolder);
        }
        self.values
            .get(&share.range.start)
            .copied()
            .ok_or(RangeRefusal::MissingShare)
    }

    fn join_share(&mut self, left: u8, right: u8, holder: ContextId) -> Result<u8, RangeRefusal> {
        let left_share = self.shares.get(&left).ok_or(RangeRefusal::MissingShare)?;
        let right_share = self.shares.get(&right).ok_or(RangeRefusal::MissingShare)?;
        if left_share.holder != Some(holder) || right_share.holder != Some(holder) {
            return Err(RangeRefusal::WrongHolder);
        }
        if left_share.parent.is_none() || left_share.parent != right_share.parent {
            return Err(RangeRefusal::NotSiblings);
        }
        let parent = left_share.parent.expect("checked parent");
        if self.shares.get(&parent).and_then(|share| share.children) != Some((left, right)) {
            return Err(RangeRefusal::NotSiblings);
        }
        self.shares.get_mut(&left).expect("checked left").holder = None;
        self.shares.get_mut(&right).expect("checked right").holder = None;
        self.shares.get_mut(&parent).expect("checked parent").holder = Some(holder);
        Ok(parent)
    }

    fn end_shared(&mut self, loan: u8, holder: ContextId) -> Result<(), RangeRefusal> {
        let record = self.loans.get(&loan).ok_or(RangeRefusal::MissingShare)?;
        if !record.active {
            return Err(RangeRefusal::ScopeEnded);
        }
        let root = self
            .shares
            .get(&record.root)
            .ok_or(RangeRefusal::MissingShare)?;
        if root.holder != Some(holder) {
            return Err(RangeRefusal::ShareStillSplit);
        }
        self.shares
            .get_mut(&record.root)
            .expect("checked root")
            .holder = None;
        self.loans.get_mut(&loan).expect("checked loan").active = false;
        Ok(())
    }

    fn recover(&mut self, loan: u8) -> Result<(), RangeRefusal> {
        let record = self.loans.get(&loan).ok_or(RangeRefusal::MissingShare)?;
        if record.active {
            return Err(RangeRefusal::ScopeStillActive);
        }
        if record.recovered {
            return Err(RangeRefusal::AlreadyRecovered);
        }
        let record = record.clone();
        if self
            .owners
            .keys()
            .any(|existing| existing.overlaps(record.range))
        {
            return Err(RangeRefusal::Overlap);
        }
        self.loans.get_mut(&loan).expect("checked loan").recovered = true;
        self.owners.insert(record.range, record.lender);
        Ok(())
    }

    fn invariant_holds(&self) -> bool {
        let owned_ranges = self.owners.keys().copied().collect::<Vec<_>>();
        if owned_ranges.iter().enumerate().any(|(index, left)| {
            owned_ranges[index + 1..]
                .iter()
                .any(|right| left.overlaps(*right))
        }) {
            return false;
        }
        for (loan_id, loan) in &self.loans {
            let Some(root) = self.shares.get(&loan.root) else {
                return false;
            };
            if root.range != loan.range || !self.range_tree_is_conserved(loan.root, loan.active) {
                return false;
            }
            if !loan.recovered && self.owners.keys().any(|range| range.overlaps(loan.range)) {
                return false;
            }
            if loan.recovered && self.owners.get(&loan.range) != Some(&loan.lender) {
                return false;
            }
            if !loan.recovered
                && self.loans.iter().any(|(other, candidate)| {
                    other != loan_id && !candidate.recovered && candidate.range == loan.range
                })
            {
                return false;
            }
        }
        true
    }

    // This helper is intentionally model-local.  The production ledger's
    // share tree is exercised by correspondence tests below, never here.
    fn range_tree_is_conserved(&self, share: u8, active: bool) -> bool {
        self.range_tree_has_active_holder(share) == Some(active)
    }

    fn range_tree_has_active_holder(&self, share: u8) -> Option<bool> {
        let record = self.shares.get(&share)?;
        if record.holder.is_some() && record.children.is_some() {
            return None;
        }
        if record.holder.is_some() {
            return Some(true);
        }
        if let Some((left, right)) = record.children {
            let left = self.range_tree_has_active_holder(left)?;
            let right = self.range_tree_has_active_holder(right)?;
            Some(left && right)
        } else {
            Some(false)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReborrowMode {
    Shared,
    // Model-only extension: the production stable-loan API intentionally has
    // no exclusive reborrow operation.
    ExclusiveModelOnly,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FieldChild {
    id: u8,
    child: ContextId,
    field: u8,
    mode: ReborrowMode,
    value: u8,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct FieldDependencyModel {
    parent: ContextId,
    values: BTreeMap<u8, u8>,
    child: Option<FieldChild>,
    next_child: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum FieldRefusal {
    MissingParent,
    ActiveChild,
    WrongChild,
    ParentSuspended,
    ChildWriteThroughShared,
}

impl FieldDependencyModel {
    fn new(parent: ContextId, fields: impl IntoIterator<Item = (u8, u8)>) -> Self {
        Self {
            parent,
            values: fields.into_iter().collect(),
            child: None,
            next_child: 0,
        }
    }

    fn reborrow(
        &mut self,
        parent: ContextId,
        child: ContextId,
        field: u8,
        mode: ReborrowMode,
    ) -> Result<u8, FieldRefusal> {
        if parent != self.parent || !self.values.contains_key(&field) {
            return Err(FieldRefusal::MissingParent);
        }
        if self.child.is_some() {
            return Err(FieldRefusal::ActiveChild);
        }
        let id = self.next_child;
        self.next_child = self.next_child.checked_add(1).expect("tiny child bound");
        let value = self.values[&field];
        self.child = Some(FieldChild {
            id,
            child,
            field,
            mode,
            value,
        });
        Ok(id)
    }

    fn parent_read(&self, parent: ContextId, field: u8) -> Result<u8, FieldRefusal> {
        if parent != self.parent {
            return Err(FieldRefusal::MissingParent);
        }
        if self
            .child
            .as_ref()
            .is_some_and(|child| child.mode == ReborrowMode::ExclusiveModelOnly)
        {
            return Err(FieldRefusal::ParentSuspended);
        }
        self.values
            .get(&field)
            .copied()
            .ok_or(FieldRefusal::MissingParent)
    }

    fn parent_write(
        &mut self,
        parent: ContextId,
        field: u8,
        value: u8,
    ) -> Result<(), FieldRefusal> {
        if parent != self.parent || !self.values.contains_key(&field) {
            return Err(FieldRefusal::MissingParent);
        }
        if self.child.as_ref().is_some_and(|child| {
            child.mode == ReborrowMode::ExclusiveModelOnly
                || (child.mode == ReborrowMode::Shared && child.field == field)
        }) {
            return Err(FieldRefusal::ParentSuspended);
        }
        self.values.insert(field, value);
        Ok(())
    }

    fn child_read(&self, child: ContextId, id: u8) -> Result<u8, FieldRefusal> {
        let loan = self.child.as_ref().ok_or(FieldRefusal::WrongChild)?;
        if loan.id != id || loan.child != child {
            return Err(FieldRefusal::WrongChild);
        }
        Ok(loan.value)
    }

    fn child_write(&mut self, child: ContextId, id: u8, value: u8) -> Result<(), FieldRefusal> {
        let loan = self.child.as_mut().ok_or(FieldRefusal::WrongChild)?;
        if loan.id != id || loan.child != child {
            return Err(FieldRefusal::WrongChild);
        }
        if loan.mode == ReborrowMode::Shared {
            return Err(FieldRefusal::ChildWriteThroughShared);
        }
        loan.value = value;
        Ok(())
    }

    // Model-only value transport: the child returns its updated field to the
    // caller before the parent dependency is discharged.
    fn end_child(&mut self, child: ContextId, id: u8) -> Result<u8, FieldRefusal> {
        let loan = self.child.take().ok_or(FieldRefusal::WrongChild)?;
        if loan.id != id || loan.child != child {
            self.child = Some(loan);
            return Err(FieldRefusal::WrongChild);
        }
        self.values.insert(loan.field, loan.value);
        Ok(loan.value)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MutexHandle {
    id: u8,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct MutexGuard {
    id: u8,
    context: ContextId,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MutexProtocolModel {
    payload: u8,
    invariant_held: bool,
    guard: Option<MutexGuard>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ProtocolRefusal {
    Unguarded,
    AlreadyGuarded,
    WrongGuard,
    CrossContext,
}

impl MutexProtocolModel {
    // Model-only protocol: this is an invariant/guard transition, not a lock.
    fn new(payload: u8) -> Self {
        Self {
            payload,
            invariant_held: true,
            guard: None,
        }
    }

    fn handle(&self) -> MutexHandle {
        MutexHandle { id: 0 }
    }

    fn acquire(
        &mut self,
        handle: MutexHandle,
        context: ContextId,
    ) -> Result<MutexGuard, ProtocolRefusal> {
        if handle.id != 0 {
            return Err(ProtocolRefusal::WrongGuard);
        }
        if self.guard.is_some() {
            return Err(ProtocolRefusal::AlreadyGuarded);
        }
        self.invariant_held = false;
        let guard = MutexGuard { id: 0, context };
        self.guard = Some(guard);
        Ok(guard)
    }

    fn read_raw(&self) -> Result<u8, ProtocolRefusal> {
        Err(ProtocolRefusal::Unguarded)
    }

    fn read_guard(&self, context: ContextId, guard: MutexGuard) -> Result<u8, ProtocolRefusal> {
        (guard.context == context && self.guard == Some(guard))
            .then_some(self.payload)
            .ok_or(ProtocolRefusal::WrongGuard)
    }

    fn write_guard(&mut self, guard: MutexGuard, value: u8) -> Result<(), ProtocolRefusal> {
        if self.guard != Some(guard) {
            return Err(ProtocolRefusal::WrongGuard);
        }
        self.payload = value;
        Ok(())
    }

    fn release(&mut self, guard: MutexGuard) -> Result<(), ProtocolRefusal> {
        if self.guard != Some(guard) {
            return Err(ProtocolRefusal::WrongGuard);
        }
        self.guard = None;
        self.invariant_held = true;
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ThreadLocalCellModel {
    home: ContextId,
    value: u8,
}

impl ThreadLocalCellModel {
    // Model-only protocol: copyability does not transfer the home context.
    fn new(home: ContextId, value: u8) -> Self {
        Self { home, value }
    }

    fn read(&self, context: ContextId) -> Result<u8, ProtocolRefusal> {
        (context == self.home)
            .then_some(self.value)
            .ok_or(ProtocolRefusal::CrossContext)
    }

    fn write(&mut self, context: ContextId, value: u8) -> Result<(), ProtocolRefusal> {
        if context != self.home {
            return Err(ProtocolRefusal::CrossContext);
        }
        self.value = value;
        Ok(())
    }

    fn transfer(&self, _to: ContextId) -> Result<(), ProtocolRefusal> {
        Err(ProtocolRefusal::CrossContext)
    }
}

fn production_memory_fact(start: u32, end: u32, own: bool) -> CResourceFact {
    let range = CMemoryRange::new(
        Pointer {
            block: "v14-buffer".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(start),
        Bitvector32Term::Constant(end),
    );
    if own {
        CResourceFact::own_memory(range)
    } else {
        CResourceFact::view_memory(range)
    }
}

fn production_checked(fact: CResourceFact) -> CCheckedResourceFact {
    CCheckedResourceFact {
        fact,
        role: CResourceTransferRole::Borrow,
        snapshot: CResourceSnapshot::Entry,
        clause_position: None,
        section_index: None,
    }
}

fn production_backing(fact: &CResourceFact) -> ResourceOccurrenceId {
    ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unique_owned_occurrence_for_fact(fact)
        .expect("model correspondence backing")
        .0
}

#[test]
fn r27_context_partition_transfer_join_allows_disjoint_writers() {
    let left_context = ContextId(0);
    let right_context = ContextId(1);
    let whole = ByteRange::new(0, 8);
    let mut model = RangeOwnershipModel::new([(whole, left_context, 0)]);
    let (left, right) = model.partition(left_context, whole, 4).unwrap();
    model.transfer(right, left_context, right_context).unwrap();
    model.write(left_context, left, 1).unwrap();
    model.write(right_context, right, 2).unwrap();
    assert_eq!(
        model.write(right_context, left, 3),
        Err(RangeRefusal::MissingOwner)
    );
    assert_eq!(
        model.join(left, right, left_context),
        Err(RangeRefusal::WrongContext)
    );
    assert!(model.invariant_holds());
}

#[test]
fn r27_reader_in_one_context_excludes_overlapping_writer_in_another() {
    let owner = ContextId(0);
    let reader_a = ContextId(1);
    let reader_b = ContextId(2);
    let range = ByteRange::new(0, 2);
    let mut model = RangeOwnershipModel::new([(range, owner, 7)]);
    let (loan, root) = model.lend_shared(owner, reader_a, range).unwrap();
    let (left, right) = model
        .split_share(root, reader_a, reader_a, reader_b)
        .unwrap();
    assert_eq!(model.read_shared(left, reader_a), Ok(7));
    assert_eq!(model.read_shared(right, reader_b), Ok(7));
    assert_eq!(
        model.write(reader_b, range, 8),
        Err(RangeRefusal::MissingOwner)
    );
    model.transfer_share(right, reader_b, reader_a).unwrap();
    model.join_share(left, right, reader_a).unwrap();
    model.end_shared(loan, reader_a).unwrap();
    model.recover(loan).unwrap();
    model.write(owner, range, 8).unwrap();
    assert!(model.invariant_holds());
}

#[test]
fn range_share_invariant_rejects_a_missing_split_child() {
    let owner = ContextId(0);
    let reader = ContextId(1);
    let range = ByteRange::new(0, 2);
    let mut model = RangeOwnershipModel::new([(range, owner, 7)]);
    let (_loan, root) = model.lend_shared(owner, reader, range).unwrap();
    let (_left, right) = model.split_share(root, reader, reader, reader).unwrap();
    model.shares.get_mut(&right).expect("split child").holder = None;
    assert!(!model.invariant_holds());
}

#[test]
fn r28_shared_and_exclusive_reborrows_preserve_parent_dependency() {
    let parent = ContextId(0);
    let child = ContextId(1);
    let mut model = FieldDependencyModel::new(parent, [(0, 4), (1, 9)]);
    let shared = model
        .reborrow(parent, child, 0, ReborrowMode::Shared)
        .unwrap();
    assert_eq!(model.parent_read(parent, 0), Ok(4));
    assert_eq!(model.child_read(child, shared), Ok(4));
    assert_eq!(
        model.parent_write(parent, 0, 5),
        Err(FieldRefusal::ParentSuspended)
    );
    assert_eq!(
        model.child_write(child, shared, 5),
        Err(FieldRefusal::ChildWriteThroughShared)
    );
    model.end_child(child, shared).unwrap();
    model.parent_write(parent, 0, 5).unwrap();

    // Extension-only exclusive reborrow: parent reads are suspended as well
    // as writes until the child returns its authority.
    let exclusive = model
        .reborrow(parent, child, 1, ReborrowMode::ExclusiveModelOnly)
        .unwrap();
    assert_eq!(
        model.parent_read(parent, 1),
        Err(FieldRefusal::ParentSuspended)
    );
    model.child_write(child, exclusive, 12).unwrap();
    assert_eq!(model.end_child(child, exclusive), Ok(12));
    assert_eq!(model.parent_read(parent, 1), Ok(12));
}

#[test]
fn r29_returned_field_loan_recovers_updated_value_after_dependency() {
    let parent = ContextId(0);
    let child = ContextId(1);
    let mut model = FieldDependencyModel::new(parent, [(7, 10)]);
    let loan = model
        .reborrow(parent, child, 7, ReborrowMode::ExclusiveModelOnly)
        .unwrap();
    model.child_write(child, loan, 99).unwrap();
    assert_eq!(
        model.parent_read(parent, 7),
        Err(FieldRefusal::ParentSuspended)
    );
    assert_eq!(model.end_child(child, loan), Ok(99));
    assert_eq!(model.parent_read(parent, 7), Ok(99));
    assert_eq!(model.end_child(child, loan), Err(FieldRefusal::WrongChild));
}

#[test]
fn r30_mutex_guard_and_thread_local_cell_protocols_are_model_only() {
    let mut mutex = MutexProtocolModel::new(3);
    let handle = mutex.handle();
    assert_eq!(mutex.read_raw(), Err(ProtocolRefusal::Unguarded));
    let guard = mutex.acquire(handle, ContextId(0)).unwrap();
    assert_eq!(
        mutex.acquire(handle, ContextId(1)),
        Err(ProtocolRefusal::AlreadyGuarded)
    );
    assert_eq!(mutex.read_guard(ContextId(0), guard), Ok(3));
    assert_eq!(
        mutex.read_guard(
            ContextId(0),
            MutexGuard {
                id: guard.id,
                context: ContextId(1),
            },
        ),
        Err(ProtocolRefusal::WrongGuard)
    );
    mutex.write_guard(guard, 11).unwrap();
    mutex.release(guard).unwrap();
    assert!(mutex.invariant_held);

    let mut cell = ThreadLocalCellModel::new(ContextId(0), 4);
    cell.write(ContextId(0), 8).unwrap();
    assert_eq!(cell.read(ContextId(0)), Ok(8));
    assert_eq!(cell.read(ContextId(1)), Err(ProtocolRefusal::CrossContext));
    assert_eq!(
        cell.write(ContextId(1), 9),
        Err(ProtocolRefusal::CrossContext)
    );
    assert_eq!(
        cell.transfer(ContextId(1)),
        Err(ProtocolRefusal::CrossContext)
    );
}

#[test]
fn two_reader_trace_places_readers_in_different_model_contexts() {
    let owner = ContextId(0);
    let first_reader = ContextId(1);
    let second_reader = ContextId(2);
    let range = ByteRange::new(0, 1);
    let mut model = RangeOwnershipModel::new([(range, owner, 0)]);
    let (loan, root) = model.lend_shared(owner, first_reader, range).unwrap();
    let (first, second) = model
        .split_share(root, first_reader, first_reader, second_reader)
        .unwrap();
    assert_eq!(model.read_shared(first, first_reader), Ok(0));
    assert_eq!(model.read_shared(second, second_reader), Ok(0));
    assert_eq!(
        model.write(second_reader, range, 1),
        Err(RangeRefusal::MissingOwner)
    );
    model
        .transfer_share(second, second_reader, first_reader)
        .unwrap();
    model.join_share(first, second, first_reader).unwrap();
    model.end_shared(loan, first_reader).unwrap();
    model.recover(loan).unwrap();
    assert!(model.invariant_holds());
}

#[test]
fn correspondence_calls_production_partition_lend_split_transfer_join() {
    let owner = ContextId(0);
    let reader = ContextId(1);
    let whole = ByteRange::new(0, 8);
    let mut model = RangeOwnershipModel::new([(whole, owner, 0)]);
    let (left, right) = model.partition(owner, whole, 4).unwrap();
    model.transfer(right, owner, reader).unwrap();
    model.write(owner, left, 1).unwrap();
    model.write(reader, right, 2).unwrap();

    let assumptions = PureFactContext::new();
    let owner_fact = production_memory_fact(0, 8, true);
    let resources = ResourceContext::new().unchecked_with_fact(owner_fact);
    let ledger = LoanLedger::new();
    let caller = ledger.fresh_participant().unwrap();
    let callee = ledger.fresh_participant().unwrap();
    let plan = plan_stable_view_transfer(
        &resources,
        &[production_checked(production_memory_fact(0, 4, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect("production planner must make the same bounded partition");
    assert_eq!(plan.stable_views.len(), 1);
    assert!(
        plan.caller_resources_after_requirements
            .facts()
            .iter()
            .any(|fact| fact == &production_memory_fact(4, 8, true))
    );

    let selected = production_memory_fact(0, 4, true);
    let opening = ledger
        .lend(caller, callee, production_backing(&selected), selected)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let (split, left_share, right_share) = ledger
        .split(opening.root_share, callee, callee, caller)
        .unwrap();
    let ledger = ledger.apply(&split).unwrap();
    assert!(ledger.permits_view(callee, &opening.description, left_share, &assumptions));
    assert!(ledger.permits_view(caller, &opening.description, right_share, &assumptions));
    let transfer = ledger.transfer(left_share, callee, caller).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let join = ledger.join(left_share, right_share, caller).unwrap();
    let ledger = ledger.apply(&join).unwrap();
    let end = ledger.end(opening.scope, caller).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    let (recover, recovered, _) = ledger.recover(opening.loan, caller).unwrap();
    assert!(recovered.is_own());
    let _ledger = ledger.apply(&recover).unwrap();
    assert!(model.invariant_holds());
}

#[test]
fn correspondence_calls_production_shared_reborrow_and_end_ordering() {
    let ledger = LoanLedger::new();
    let parent_holder = ledger.fresh_participant().unwrap();
    let child_holder = ledger.fresh_participant().unwrap();
    let fact = CResourceFact::own_token("v14-parent".to_string(), Vec::new());
    let opening = ledger
        .lend(
            parent_holder,
            parent_holder,
            production_backing(&fact),
            fact,
        )
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: opening.description.support(),
        viewed: opening.description.viewed().clone(),
        hold: None,
    };
    let child = ledger
        .reborrow(binding, parent_holder, child_holder)
        .unwrap();
    let ledger = ledger.apply(&child.transition).unwrap();
    assert_eq!(
        ledger.end(opening.scope, parent_holder),
        Err(LoanRefusal::ActiveDependency)
    );
    let returned = ledger
        .transfer(child.root_share, child_holder, parent_holder)
        .unwrap();
    let ledger = ledger.apply(&returned).unwrap();
    let child_end = ledger.end(child.scope, parent_holder).unwrap();
    let ledger = ledger.apply(&child_end).unwrap();
    let parent_end = ledger.end(opening.scope, parent_holder).unwrap();
    let _ledger = ledger.apply(&parent_end).unwrap();
}
