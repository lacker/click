//! Executable design model for stable shared loans.
//!
//! This is deliberately independent of the production loan ledger. It fixes
//! the conservation laws and cross-context counterexamples before the kernel
//! representation is used by C contract transfer.

use std::collections::{BTreeMap, BTreeSet};

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
