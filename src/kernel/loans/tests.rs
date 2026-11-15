use super::*;
use crate::kernel::{ConditionTerm, Pointer, PointerOffsetTerm, Resource, ResourceFact, Variable};

fn owned(name: &str) -> ResourceFact {
    ResourceFact::own(Resource::Token {
        name: name.to_string(),
        arguments: Vec::new().into(),
    })
}

fn backing(fact: &ResourceFact) -> ResourceOccurrenceId {
    ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unique_owned_occurrence_for_fact(fact)
        .unwrap()
        .0
}

fn lend_test(
    ledger: &LoanLedger,
    lender: LoanParticipantId,
    borrower: LoanParticipantId,
    escrow: ResourceFact,
) -> LoanOpening {
    ledger
        .lend(lender, borrower, backing(&escrow), escrow)
        .unwrap()
}

fn participants() -> (LoanLedger, LoanParticipantId, LoanParticipantId) {
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    (ledger, owner, reader)
}

fn opaque_memory_borrow_fixture() -> (ResourceFact, CheckedResourceFact) {
    let pointer = crate::kernel::PointerValue::new(
        Pointer::symbolic(Variable(9_819_001)),
        crate::kernel::ProgramType::Int32Pointer,
    );
    let owner =
        crate::kernel::MemoryRange::from_pointer_value(&pointer, 0u32.into(), 4u32.into(), 4);
    let requested = crate::kernel::MemoryRange::from_pointer_value(
        &pointer.with_root_extent(),
        1u32.into(),
        2u32.into(),
        4,
    );
    (
        ResourceFact::own_memory(owner),
        checked(ResourceFact::own_memory(requested)),
    )
}

#[test]
fn concrete_view_recovery_retains_the_callers_opaque_carrier() {
    let _session = crate::kernel::VerificationSession::enter();
    let assumptions = PureFactContext::new();
    let (owner, requested) = opaque_memory_borrow_fixture();
    let requested = requested.fact.memory_own_range().unwrap();
    let first = checked(ResourceFact::view_memory(requested.clone()));
    let second = checked(ResourceFact::view_memory(
        crate::kernel::MemoryRange::new_with_element_width(
            requested.base().clone(),
            2u32.into(),
            3u32.into(),
            4,
        )
        .with_carrier_of(requested),
    ));
    for views in [vec![first.clone()], vec![first.clone(), second]] {
        let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let (ledger, caller, callee) = participants();
        let plan =
            plan_stable_view_transfer(&resources, &views, &assumptions, &ledger, caller, callee)
                .unwrap();
        assert!(
            !plan
                .caller_resources_after_requirements
                .satisfies_fact(&owner, &assumptions)
        );
        assert!(
            !plan
                .callee_resources
                .satisfies_fact(&ResourceFact::own_memory(requested.clone()), &assumptions,)
        );
        let recovery = plan
            .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
            .unwrap();
        assert!(
            recovery.resources.satisfies_fact(&owner, &assumptions),
            "recovery must restore the original opaque owner after {} view(s)",
            views.len()
        );
    }
}

#[test]
fn partial_owned_borrow_returns_only_its_slice_with_the_callers_opaque_domain() {
    let _session = crate::kernel::VerificationSession::enter();
    let assumptions = PureFactContext::new();
    let (owner, requested) = opaque_memory_borrow_fixture();
    let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &resources,
        std::slice::from_ref(&requested),
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let returned = plan.canonical_transferred_ownership[0]
        .as_ref()
        .expect("borrowed slice retains its caller domain");
    let returned_range = returned.memory_own_range().unwrap();
    assert_eq!(returned_range.start(), &1u32.into());
    assert_eq!(returned_range.end(), &2u32.into());
    assert_eq!(
        returned_range.access_designation(),
        owner.memory_own_range().unwrap().access_designation()
    );
    assert!(!plan.callee_resources.satisfies_fact(&owner, &assumptions));
    let restored = plan
        .caller_resources_after_requirements
        .clone()
        .try_compose_with_fact(returned.clone(), &assumptions)
        .unwrap();
    assert!(restored.satisfies_fact(&owner, &assumptions));
    assert!(
        plan_stable_view_transfer(
            &ResourceContext::new(),
            std::slice::from_ref(&requested),
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .is_err()
    );
    let viewed = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
        owner.memory_own_range().unwrap().clone(),
    ));
    assert!(
        plan_stable_view_transfer(&viewed, &[requested], &assumptions, &ledger, caller, callee,)
            .is_err()
    );
}

#[test]
fn borrowed_contract_input_is_read_only_and_cannot_be_closed_or_recovered() {
    let (ledger, holder, _) = participants();
    let assumptions = PureFactContext::new();
    let viewed = memory(0, 4, false);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .borrowed_contract_input(holder, support, viewed.clone(), None)
        .expect("checked contract input");
    let ledger = ledger.apply(&opening.transition).expect("apply input root");

    assert!(ledger.invariant_holds());
    assert!(ledger.permits_view(
        holder,
        &opening.description,
        opening.root_share,
        &assumptions,
    ));
    assert_eq!(
        ledger.permits_memory_access(viewed.memory_range().unwrap()),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(
        ledger.end(opening.scope, holder),
        Err(LoanRefusal::WrongHolder)
    );
    assert_eq!(
        ledger.recover(opening.loan, holder),
        Err(LoanRefusal::InvalidEvidence)
    );
}

fn parameter_range(variable: u64, start: u32, end: u32, width: u32) -> MemoryRange {
    MemoryRange::new_with_element_width(
        crate::kernel::Pointer {
            block: PointerBlock::ExternalArgument,
            offset: crate::kernel::PointerOffsetTerm::Variable(Variable(variable)),
        },
        MachineTerm::constant(start),
        MachineTerm::constant(end),
        width,
    )
}

fn local_job_range() -> MemoryRange {
    MemoryRange::new_with_element_width(
        crate::kernel::Pointer {
            block: "local:job".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(4),
        4,
    )
}

#[test]
fn symbolic_external_write_is_distinct_from_a_fresh_local_loan() {
    let assumptions = PureFactContext::new();
    let (ledger, owner, reader) = participants();
    let job = ResourceFact::own_memory(local_job_range());
    let opening = lend_test(&ledger, owner, reader, job);
    let ledger = ledger.apply(&opening.transition).unwrap();
    assert!(ledger.invariant_holds());
    assert!(
        local_job_range()
            .base()
            .blocks_proven_distinct(parameter_range(7, 0, 1, 4).base())
    );
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(7, 0, 1, 4), &assumptions,),
        Ok(())
    );
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&local_job_range(), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    let returned = ledger.transfer(opening.root_share, reader, owner).unwrap();
    let ledger = ledger.apply(&returned).unwrap();
    let ended = ledger.end(opening.scope, owner).unwrap();
    let ledger = ledger.apply(&ended).unwrap();
    assert!(ledger.invariant_holds());
}

#[test]
fn symbolic_external_write_still_refuses_a_nonlocal_indexed_loan() {
    let assumptions = PureFactContext::new();
    let (ledger, owner, reader) = participants();
    let job = lend_test(
        &ledger,
        owner,
        reader,
        ResourceFact::own_memory(local_job_range()),
    );
    let ledger = ledger.apply(&job.transition).unwrap();
    let global = lend_test(&ledger, owner, reader, memory(0, 4, true));
    let ledger = ledger.apply(&global.transition).unwrap();
    assert!(ledger.invariant_holds());
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(7, 0, 1, 4), &assumptions,),
        Err(LoanRefusal::UnsupportedPartition)
    );
}

#[test]
fn symbolic_external_write_still_refuses_a_second_symbolic_loan() {
    let assumptions = PureFactContext::new();
    let (ledger, owner, _, _) = rooted_parameter_view(41);
    let reader = ledger.fresh_participant().unwrap();
    let job = lend_test(
        &ledger,
        owner,
        reader,
        ResourceFact::own_memory(local_job_range()),
    );
    let ledger = ledger.apply(&job.transition).unwrap();
    assert!(ledger.invariant_holds());
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(42, 0, 1, 4), &assumptions,),
        Err(LoanRefusal::UnsupportedPartition)
    );
}

fn rooted_parameter_view(
    variable: u64,
) -> (LoanLedger, LoanParticipantId, LoanOpening, ResourceFact) {
    let (ledger, holder, _) = participants();
    let viewed = ResourceFact::view_memory(parameter_range(variable, 0, 1, 4));
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .borrowed_contract_input(holder, support, viewed.clone(), None)
        .expect("checked symbolic contract input");
    let ledger = ledger
        .apply(&opening.transition)
        .expect("apply symbolic root");
    (ledger, holder, opening, viewed)
}

/// A contract input over parameter memory has a symbolic base offset, so
/// it cannot enter the concrete index; it is still a live loan that
/// refuses writes proven to touch it and rejects closure and recovery.
#[test]
fn symbolic_borrowed_contract_input_is_live_outside_the_concrete_index() {
    let assumptions = PureFactContext::new();
    let (ledger, holder, opening, _) = rooted_parameter_view(41);
    assert!(
        ledger.has_indexed_memory_overlap(&parameter_range(41, 0, 1, 4)),
        "an exact symbolic origin is indexed without a loan search"
    );
    assert!(ledger.has_indexed_memory_overlap(&parameter_range(41, 3, 4, 1)));
    assert!(ledger.has_indexed_memory_overlap(&parameter_range(41, 0, 8, 1)));
    assert!(!ledger.has_indexed_memory_overlap(&parameter_range(41, 4, 8, 1)));
    assert!(!ledger.has_indexed_memory_overlap(&parameter_range(42, 0, 1, 4)));
    assert!(ledger.invariant_holds());
    assert!(ledger.has_active_memory_loans());
    assert!(ledger.permits_view(
        holder,
        &opening.description,
        opening.root_share,
        &assumptions,
    ));
    // The viewed cell itself, at any element width that touches it.
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(41, 0, 1, 4), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(41, 3, 4, 1), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(41, 0, 8, 1), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    // A concretely disjoint offset of the same object.
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(41, 1, 2, 4), &assumptions),
        Ok(())
    );
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(41, 4, 8, 1), &assumptions),
        Ok(())
    );
    // Another parameter, separate by the contract partition unless the
    // path proves otherwise; and storage this activation declared.
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(42, 0, 1, 4), &assumptions),
        Ok(())
    );
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(
            memory(0, 1, true).memory_range().unwrap(),
            &assumptions
        ),
        Ok(())
    );
    assert_eq!(
        ledger.end(opening.scope, holder),
        Err(LoanRefusal::WrongHolder)
    );
    assert_eq!(
        ledger.recover(opening.loan, holder),
        Err(LoanRefusal::InvalidEvidence)
    );
}

/// A concrete query is refused while a symbolic loan on its block is
/// live only when the overlap is proven; a symbolic query is refused
/// outright while any concrete loan is indexed, because the index cannot
/// answer it.
#[test]
fn symbolic_and_concrete_loans_fail_closed_across_the_index_boundary() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let concrete = lend_test(&ledger, owner, reader, memory(0, 4, true));
    let ledger = ledger.apply(&concrete.transition).unwrap();
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(7, 0, 1, 4), &assumptions),
        Err(LoanRefusal::UnsupportedPartition)
    );
    let ended = ledger
        .transfer(concrete.root_share, reader, owner)
        .and_then(|transfer| ledger.apply(&transfer))
        .and_then(|ledger| ledger.end(concrete.scope, owner).map(|end| (ledger, end)))
        .and_then(|(ledger, end)| ledger.apply(&end))
        .expect("close the concrete loan");
    assert!(ended.invariant_holds());
    assert_eq!(
        ended.permits_memory_access_with_assumptions(&parameter_range(7, 0, 1, 4), &assumptions),
        Ok(())
    );
}

/// A concrete block range at one offset, at an explicit element width.
fn buffer_range(start: u32, end: u32, width: u32) -> MemoryRange {
    MemoryRange::new_with_element_width(
        crate::kernel::Pointer {
            block: "buffer".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(start),
        MachineTerm::constant(end),
        width,
    )
}

/// Loans and accesses are compared bytewise, so a mismatched element
/// width can neither hide an overlap nor manufacture one. The ledger
/// holds a width-4 loan over bytes 0..4 and a width-1 loan over byte 5;
/// byte 4 is the gap between them, and it separates the accepted
/// mismatched-width queries from the refused ones (R08's width-crossing
/// case; docs/internals/stable-views.md).
#[test]
fn bytewise_overlap_is_decided_across_mismatched_element_widths() {
    let (ledger, owner, reader) = participants();
    // Bytes 0..4, spelled as one width-4 element.
    let wide = lend_test(
        &ledger,
        owner,
        reader,
        ResourceFact::own_memory(buffer_range(0, 1, 4)),
    );
    let ledger = ledger.apply(&wide.transition).unwrap();
    // Byte 5, spelled as one width-1 element.
    let narrow = lend_test(
        &ledger,
        owner,
        reader,
        ResourceFact::own_memory(buffer_range(5, 6, 1)),
    );
    let ledger = ledger.apply(&narrow.transition).unwrap();
    assert!(ledger.invariant_holds());

    // A width-1 access at byte 2, inside the width-4 loan.
    assert_eq!(
        ledger.permits_memory_access(&buffer_range(2, 3, 1)),
        Err(LoanRefusal::ActiveDependency)
    );
    // The reverse direction: a width-4 access covering bytes 4..8, which
    // contains the width-1 loan's byte 5.
    assert_eq!(
        ledger.permits_memory_access(&buffer_range(1, 2, 4)),
        Err(LoanRefusal::ActiveDependency)
    );
    // Byte 4 alone: mismatched widths against both loans, no shared byte.
    assert_eq!(ledger.permits_memory_access(&buffer_range(4, 5, 1)), Ok(()));
    // Bytes 8..12 at width 4: past both loans.
    assert_eq!(ledger.permits_memory_access(&buffer_range(2, 3, 4)), Ok(()));
}

/// Ending a child scope over a symbolic root leaves the root's
/// protection in place, and the invariant tracks the symbolic entries.
#[test]
fn child_reborrow_of_a_symbolic_root_keeps_the_root_protected() {
    let (ledger, holder, _) = participants();
    let reader = ledger.fresh_participant().unwrap();
    let assumptions = PureFactContext::new();
    let viewed = ResourceFact::view_memory(parameter_range(9, 0, 1, 4));
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .borrowed_contract_input(holder, support, viewed.clone(), None)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let parent = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed,
        hold: None,
    };
    let child = ledger.reborrow(parent, holder, reader).unwrap();
    let ledger = ledger.apply(&child.transition).unwrap();
    assert!(ledger.invariant_holds());
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(9, 0, 1, 4), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    let transfer = ledger.transfer(child.root_share, reader, holder).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let end = ledger.end(child.scope, holder).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    assert!(ledger.invariant_holds());
    assert!(ledger.has_active_memory_loans());
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&parameter_range(9, 0, 1, 4), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
}

/// Projection extends a composite loan's permitted descriptions by a
/// checked child without changing the ledger's identity; it needs a
/// permitted composite parent and a live scope, and never admits an
/// exclusive instance.
#[test]
fn projection_extends_permitted_descriptions_without_a_transition() {
    let (ledger, owner, reader) = participants();
    let head = composite("cell", true);
    let support = backing(&head);
    let nested = composite("nested", true);
    let backing_pieces =
        CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![nested]).unwrap();
    let opening = ledger
        .lend_composite(owner, reader, support, head, backing_pieces)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let assumptions = PureFactContext::new();
    let nested_view = composite("nested", false);
    let deep = ResourceFact::view_memory(memory(0, 1, true).memory_range().unwrap().clone());
    let describe = |viewed: ResourceFact| StableViewDescription {
        loan: opening.loan,
        support,
        viewed,
    };
    assert!(ledger.permits_view(
        reader,
        &describe(nested_view.clone()),
        opening.root_share,
        &assumptions
    ));
    assert!(!ledger.permits_view(
        reader,
        &describe(deep.clone()),
        opening.root_share,
        &assumptions
    ));
    let evidence = CompositeProjectionEvidence::from_checked_expansion(
        nested_view.clone(),
        vec![deep.clone()],
    )
    .expect("a viewed one-level expansion is projection evidence");
    let projected = ledger
        .project(reader, opening.loan, &nested_view, &evidence, deep.clone())
        .expect("a child of a permitted composite view projects");
    assert_eq!(projected, ledger, "projection keeps the ledger identity");
    assert!(projected.permits_view(
        reader,
        &describe(deep.clone()),
        opening.root_share,
        &assumptions
    ));
    assert!(projected.invariant_holds());
    // Not a permitted parent, an owned child, and an ended scope.
    let other_view = composite("other", false);
    let other_evidence =
        CompositeProjectionEvidence::from_checked_expansion(other_view.clone(), vec![deep.clone()])
            .expect("a viewed one-level expansion is projection evidence");
    assert_eq!(
        projected.project(
            reader,
            opening.loan,
            &other_view,
            &other_evidence,
            deep.clone()
        ),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert_eq!(
        projected.project(
            reader,
            opening.loan,
            &nested_view,
            &evidence,
            memory(0, 1, true)
        ),
        Err(LoanRefusal::UnsupportedResource)
    );
    // The evidence must expand the very parent the loan permits, and the
    // child must be one that expansion contains (docs/internals/stable-views.md).
    assert_eq!(
        projected.project(
            reader,
            opening.loan,
            &nested_view,
            &other_evidence,
            deep.clone()
        ),
        Err(LoanRefusal::InvalidEvidence),
        "evidence for another composite cannot authorize this parent"
    );
    let sibling = ResourceFact::view_memory(memory(4, 5, true).memory_range().unwrap().clone());
    assert_eq!(
        projected.project(reader, opening.loan, &nested_view, &evidence, sibling),
        Err(LoanRefusal::MissingBacking),
        "a child the checked expansion does not contain is refused"
    );
    let transfer = projected
        .transfer(opening.root_share, reader, owner)
        .unwrap();
    let projected = projected.apply(&transfer).unwrap();
    let end = projected.end(opening.scope, owner).unwrap();
    let ended = projected.apply(&end).unwrap();
    assert_eq!(
        ended.project(owner, opening.loan, &nested_view, &evidence, deep),
        Err(LoanRefusal::ScopeEnded)
    );
}

/// A projection is derived read-only authority: it keeps the ledger
/// identity, changes only what the loan permits, and mints no share, no
/// scope, and no recovery right. No transition is reachable from a
/// projected description alone (the identity rule on `project`, F4).
#[test]
fn a_projection_mints_no_share_and_keeps_the_ledger_identity() {
    let (ledger, owner, reader) = participants();
    let head = composite("cell", true);
    let support = backing(&head);
    let nested = composite("nested", true);
    let backing_pieces =
        CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![nested]).unwrap();
    let opening = ledger
        .lend_composite(owner, reader, support, head, backing_pieces)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let assumptions = PureFactContext::new();
    let nested_view = composite("nested", false);
    let deep = ResourceFact::view_memory(memory(0, 1, true).memory_range().unwrap().clone());
    let describe = |viewed: ResourceFact| StableViewDescription {
        loan: opening.loan,
        support,
        viewed,
    };
    let evidence = CompositeProjectionEvidence::from_checked_expansion(
        nested_view.clone(),
        vec![deep.clone()],
    )
    .unwrap();
    let projected = ledger
        .project(reader, opening.loan, &nested_view, &evidence, deep.clone())
        .unwrap();
    // Equal ledgers, different derived descriptions: identity tracks
    // authority-changing transitions only.
    assert_eq!(projected, ledger);
    assert!(!ledger.permits_view(
        reader,
        &describe(deep.clone()),
        opening.root_share,
        &assumptions
    ));
    assert!(projected.permits_view(
        reader,
        &describe(deep.clone()),
        opening.root_share,
        &assumptions
    ));
    let projected_binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: deep.clone(),
        hold: None,
    };
    // The projection carries no share of its own, so every
    // transition-bearing operation still needs the authority the loan
    // already had: the borrower's share, the lender's close right, and
    // the escrow's recovery right.
    assert_eq!(
        projected.reborrow(projected_binding.clone(), owner, reader),
        Err(LoanRefusal::MissingLoanBinding),
        "a projected description does not hand its holder's share to another participant"
    );
    assert_eq!(
        projected.validate_view_binding(projected_binding, owner),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert_eq!(
        projected.lend(owner, reader, support, deep.clone()),
        Err(LoanRefusal::NotOwnership),
        "a projected view is not ownership to lend"
    );
    assert_eq!(
        projected.transfer(opening.root_share, owner, reader),
        Err(LoanRefusal::WrongHolder)
    );
    assert_eq!(
        projected.end(opening.scope, reader),
        Err(LoanRefusal::WrongHolder)
    );
    assert_eq!(
        projected.recover(opening.loan, owner),
        Err(LoanRefusal::ScopeStillActive)
    );
    assert!(projected.invariant_holds());
}

/// A reborrow is authorized by one description, so the child loan
/// permits that description alone: it cannot describe the parent's head
/// or a sibling child of it (docs/internals/stable-views.md).
#[test]
fn a_reborrow_narrows_to_the_description_that_authorized_it() {
    let (ledger, owner, reader) = participants();
    let borrower = ledger.fresh_participant().unwrap();
    let assumptions = PureFactContext::new();
    let head = composite("cell", true);
    let support = backing(&head);
    let sibling = memory(0, 4, true);
    let nested = composite("nested", true);
    let backing_pieces = CompositeLoanBacking::from_checked_expansion(
        support,
        head.clone(),
        vec![sibling.clone(), nested],
    )
    .unwrap();
    let opening = ledger
        .lend_composite(owner, reader, support, head.clone(), backing_pieces)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let head_view = composite("cell", false);
    let sibling_view = ResourceFact::view_memory(sibling.memory_range().unwrap().clone());
    let nested_view = composite("nested", false);
    let deep = ResourceFact::view_memory(memory(8, 9, true).memory_range().unwrap().clone());
    let evidence = CompositeProjectionEvidence::from_checked_expansion(
        nested_view.clone(),
        vec![deep.clone()],
    )
    .unwrap();
    let ledger = ledger
        .project(reader, opening.loan, &nested_view, &evidence, deep.clone())
        .unwrap();
    let parent = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: nested_view.clone(),
        hold: None,
    };
    let child = ledger.reborrow(parent, reader, borrower).unwrap();
    let ledger = ledger.apply(&child.transition).unwrap();
    assert!(ledger.invariant_holds());
    let describe = |viewed: ResourceFact| StableViewDescription {
        loan: child.loan,
        support,
        viewed,
    };
    assert!(ledger.permits_view(
        borrower,
        &describe(nested_view),
        child.root_share,
        &assumptions
    ));
    for wider in [head_view, sibling_view, deep.clone()] {
        assert!(
            !ledger.permits_view(borrower, &describe(wider), child.root_share, &assumptions),
            "a child scope reborrowed from one description cannot describe the rest of the parent loan"
        );
    }
    // A nested composite child has no byte backing of its own; the
    // parent entry keeps protecting those bytes, and the child is still
    // counted by the barrier predicate.
    let child_record = ledger.storage.data.loans.get(&child.loan).unwrap();
    assert!(child_record.memory_backing.is_empty());
    assert_eq!(
        ledger
            .permits_memory_access_with_assumptions(sibling.memory_range().unwrap(), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    let transfer = ledger.transfer(child.root_share, borrower, reader).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let end = ledger.end(child.scope, reader).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    assert!(ledger.invariant_holds());
    assert!(ledger.has_active_memory_loans());
    assert_eq!(
        ledger
            .permits_memory_access_with_assumptions(sibling.memory_range().unwrap(), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    // The same holds for a reborrow of a projected child: it authorizes
    // that description and nothing else of the loan it came from.
    let projected_parent = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: deep.clone(),
        hold: None,
    };
    let grandchild = ledger.reborrow(projected_parent, reader, borrower).unwrap();
    let ledger = ledger.apply(&grandchild.transition).unwrap();
    assert!(ledger.invariant_holds());
    let describe = |viewed: ResourceFact| StableViewDescription {
        loan: grandchild.loan,
        support,
        viewed,
    };
    assert!(ledger.permits_view(
        borrower,
        &describe(deep),
        grandchild.root_share,
        &assumptions
    ));
    for wider in [
        composite("cell", false),
        ResourceFact::view_memory(sibling.memory_range().unwrap().clone()),
        composite("nested", false),
    ] {
        assert!(
            !ledger.permits_view(
                borrower,
                &describe(wider),
                grandchild.root_share,
                &assumptions
            ),
            "a reborrow of one projected child cannot describe the head or a sibling"
        );
    }
}

/// A reborrow of a memory view protects exactly the viewed bytes: it
/// registers the viewed range and nothing else of the parent's backing,
/// and ending it leaves the parent's own ranges protected (F5).
#[test]
fn a_reborrow_of_a_memory_view_protects_exactly_the_viewed_bytes() {
    let (ledger, owner, reader) = participants();
    let borrower = ledger.fresh_participant().unwrap();
    let assumptions = PureFactContext::new();
    let head = composite("cell", true);
    let support = backing(&head);
    let viewed_piece = memory(0, 4, true);
    let other_piece = memory(8, 12, true);
    let backing_pieces = CompositeLoanBacking::from_checked_expansion(
        support,
        head.clone(),
        vec![viewed_piece.clone(), other_piece.clone()],
    )
    .unwrap();
    let opening = ledger
        .lend_composite(owner, reader, support, head, backing_pieces)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let viewed = ResourceFact::view_memory(viewed_piece.memory_range().unwrap().clone());
    let parent = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: viewed.clone(),
        hold: None,
    };
    let child = ledger.reborrow(parent, reader, borrower).unwrap();
    let ledger = ledger.apply(&child.transition).unwrap();
    assert!(ledger.invariant_holds());
    let child_record = ledger.storage.data.loans.get(&child.loan).unwrap();
    assert_eq!(
        child_record.memory_backing,
        vec![viewed_piece.memory_range().unwrap().clone()],
        "the child protects the viewed range, not the parent's other pieces"
    );
    assert_eq!(child_record.permitted, vec![viewed]);
    for range in [
        viewed_piece.memory_range().unwrap(),
        other_piece.memory_range().unwrap(),
    ] {
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(range, &assumptions),
            Err(LoanRefusal::ActiveDependency)
        );
    }
    let transfer = ledger.transfer(child.root_share, borrower, reader).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let end = ledger.end(child.scope, reader).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    assert!(ledger.invariant_holds());
    for range in [
        viewed_piece.memory_range().unwrap(),
        other_piece.memory_range().unwrap(),
    ] {
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(range, &assumptions),
            Err(LoanRefusal::ActiveDependency),
            "the parent composite loan still protects its whole frontier"
        );
    }
}

/// A reborrow of a byte-less composite loan is counted and uncounted by
/// the same predicate, so ending the child leaves the parent's
/// contribution to the fail-closed barrier in place (docs/internals/stable-views.md).
#[test]
fn ending_a_reborrow_of_a_byteless_composite_loan_keeps_the_barrier_armed() {
    let (ledger, owner, reader) = participants();
    let head = ResourceFact::own(Resource::Composite {
        name: "box".to_string(),
        arguments: Vec::new().into(),
    });
    let piece = owned("box_token");
    let support = backing(&head);
    let backing = CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![piece])
        .expect("a token-only frontier is a checked expansion");
    let opening = ledger
        .lend_composite(owner, reader, support, head.clone(), backing)
        .expect("composite lend");
    let ledger = ledger.apply(&opening.transition).unwrap();
    assert!(ledger.has_active_memory_loans());
    assert!(ledger.invariant_holds());
    let parent = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: ResourceFact::view_composite("box".to_string(), Vec::new()),
        hold: None,
    };
    let child = ledger.reborrow(parent, reader, owner).unwrap();
    let ledger = ledger.apply(&child.transition).unwrap();
    assert!(ledger.has_active_memory_loans());
    assert!(ledger.invariant_holds());
    let transfer = ledger.transfer(child.root_share, owner, reader).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let end = ledger.end(child.scope, reader).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    assert!(
        ledger.has_active_memory_loans(),
        "the parent composite loan is still live"
    );
    assert!(ledger.invariant_holds());
    let transfer = ledger.transfer(opening.root_share, reader, owner).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let end = ledger.end(opening.scope, owner).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    assert!(!ledger.has_active_memory_loans());
    assert!(ledger.invariant_holds());
}

fn mutex_owner(epoch: Option<u64>) -> ResourceFact {
    ResourceFact::own(Resource::MutexLive(crate::kernel::MutexIdentity {
        mutex: crate::kernel::Pointer {
            block: "mutex".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        epoch,
    }))
}

fn abstract_mutex_input() -> (
    LoanLedger,
    LoanParticipantId,
    MutexUseContractInput,
    ResourceFact,
) {
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    let live = mutex_owner(None);
    let Resource::MutexLive(identity) = live.resource() else {
        unreachable!()
    };
    let (ledger, input) = ledger
        .borrowed_mutex_use_input(
            holder,
            backing(&owned("input clause")),
            identity.mutex.clone(),
        )
        .unwrap();
    let live = ledger
        .mutex_use_identity_description(input.usage, holder)
        .unwrap()
        .clone();
    (ledger, holder, input, live)
}

#[test]
fn assumed_use_initializations_cannot_be_exchanged_between_sibling_roots() {
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    let support = backing(&owned("same principal input"));
    let mutex = Pointer::symbolic(Variable(901));
    let (left, left_input) = ledger
        .borrowed_mutex_use_input(holder, support, mutex.clone())
        .unwrap();
    let (right, right_input) = ledger
        .borrowed_mutex_use_input(holder, support, mutex)
        .unwrap();
    // Both branches reserve the same share coordinates. Their lifetime
    // identities still differ and must be part of the owned use atom.
    assert_eq!(left_input.usage, right_input.usage);
    let left_fact = left.mutex_use_resource(left_input.usage, holder).unwrap();
    let right_fact = right.mutex_use_resource(right_input.usage, holder).unwrap();
    assert_ne!(left_fact, right_fact);
    assert!(
        right
            .check_mutex_use_input_return(
                &right_input,
                holder,
                &ResourceContext::new().unchecked_with_fact(left_fact)
            )
            .is_err()
    );
    let left_owner = left
        .mutex_use_identity_description(left_input.usage, holder)
        .unwrap();
    let right_owner = right
        .mutex_use_identity_description(right_input.usage, holder)
        .unwrap();
    assert_ne!(left_owner, right_owner);
    assert!(
        right
            .hold_mutex_use(right_input.usage, left_owner, holder)
            .is_err()
    );
    assert!(
        right
            .hold_mutex_use(right_input.usage, right_owner, holder)
            .is_ok()
    );
    let helper = left.fresh_participant().unwrap();
    let (nested, child) = left
        .reborrow_mutex_use(left_input.usage, holder, helper)
        .unwrap();
    assert_eq!(
        nested
            .mutex_use_identity_description(child.usage, helper)
            .unwrap(),
        left_owner
    );
}

#[test]
fn mutex_contract_input_has_use_but_no_owner_view_close_or_recovery_right() {
    let (ledger, holder, input, description) = abstract_mutex_input();
    let fact = ledger.mutex_use_resource(input.usage, holder).unwrap();
    let resources = ResourceContext::new().unchecked_with_fact(fact);
    assert!(ledger.invariant_holds());
    assert!(
        ledger
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_ok()
    );
    assert!(!resources.satisfies_fact(&description, &PureFactContext::new()));
    assert!(ledger.permitted_descriptions(input.usage.0.loan).is_empty());
    assert!(!ledger.has_active_memory_loans());
    let record = ledger.storage.data.loans.get(&input.usage.0.loan).unwrap();
    assert!(record.escrow.is_none());
    assert!(ledger.end(input.usage.0.scope, holder).is_err());
    assert!(ledger.recover(input.usage.0.loan, holder).is_err());
    let forged_receipt = MutexUseLoan {
        scope: input.usage.0.scope,
        loan: input.usage.0.loan,
        usage: input.usage,
    };
    assert!(ledger.recover_mutex_use(&forged_receipt, holder).is_err());
    assert!(ledger.end_mutex_reborrow(&forged_receipt, holder).is_err());
    assert!(
        mutex_calls::MutexUseCallTransfer::prepare(
            &ledger,
            holder,
            holder,
            &resources,
            &description,
            &PureFactContext::new()
        )
        .is_err()
    );
    assert!(
        ledger
            .hold_mutex_use(input.usage, &mutex_owner(None), holder)
            .is_err()
    );
    let (held, hold) = ledger
        .hold_mutex_use(input.usage, &description, holder)
        .unwrap();
    assert_eq!(
        held.check_mutex_use_input_return(&input, holder, &resources),
        Err(LoanRefusal::ActiveDependency)
    );
    let returned = held.release(hold, holder).unwrap();
    assert!(
        returned
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_ok()
    );
}

#[test]
fn mutex_contract_input_nested_helper_returns_exact_parent_without_closing_root() {
    let (ledger, holder, input, description) = abstract_mutex_input();
    let helper = ledger.fresh_participant().unwrap();
    let original = ledger.mutex_use_resource(input.usage, holder).unwrap();
    let resources = ResourceContext::new().unchecked_with_fact(original.clone());
    let (ledger, child) = ledger
        .reborrow_mutex_use(input.usage, holder, helper)
        .unwrap();
    assert!(
        ledger
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_err()
    );
    let (ledger, hold) = ledger
        .hold_mutex_use(child.usage, &description, helper)
        .unwrap();
    let ledger = ledger
        .apply(
            &ledger
                .transfer(child.usage.0.share, helper, holder)
                .unwrap(),
        )
        .unwrap();
    assert!(
        ledger
            .end_mutex_reborrow_with_parent(&child, holder)
            .is_err()
    );
    assert!(ledger.release(hold, holder).is_err());
    let ledger = ledger.release(hold, helper).unwrap();
    let (ledger, restored) = ledger
        .end_mutex_reborrow_with_parent(&child, holder)
        .unwrap();
    assert_eq!(restored, original);
    assert!(ledger.invariant_holds());
    assert!(
        ledger
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_ok()
    );
    assert!(ledger.mutex_use_resource(child.usage, holder).is_err());
    assert!(ledger.end(input.usage.0.scope, holder).is_err());
}

#[test]
fn mutex_contract_input_return_requires_exact_owned_root_and_current_holder() {
    let (ledger, holder, input, description) = abstract_mutex_input();
    let fact = ledger.mutex_use_resource(input.usage, holder).unwrap();
    assert_eq!(
        ledger.check_mutex_use_input_return(&input, holder, &ResourceContext::new()),
        Err(LoanRefusal::MissingBacking)
    );
    let duplicate = ResourceContext::new()
        .unchecked_with_fact(fact.clone())
        .unchecked_with_fact(fact.clone());
    assert!(
        ledger
            .check_mutex_use_input_return(&input, holder, &duplicate)
            .is_err()
    );
    let Resource::MutexLive(identity) = description.resource() else {
        unreachable!()
    };
    let (ledger, other) = ledger
        .borrowed_mutex_use_input(
            holder,
            backing(&owned("other clause")),
            identity.mutex.clone(),
        )
        .unwrap();
    let other_fact = ledger.mutex_use_resource(other.usage, holder).unwrap();
    assert_ne!(fact, other_fact);
    let other_resources = ResourceContext::new().unchecked_with_fact(other_fact);
    assert!(
        ledger
            .check_mutex_use_input_return(&input, holder, &other_resources)
            .is_err()
    );
    let foreign = LoanLedger::new().fresh_participant().unwrap();
    assert!(ledger.mutex_use_resource(input.usage, foreign).is_err());
    let receiver = ledger.fresh_participant().unwrap();
    let moved = ledger
        .apply(
            &ledger
                .transfer(input.usage.0.share, holder, receiver)
                .unwrap(),
        )
        .unwrap();
    let resources = ResourceContext::new().unchecked_with_fact(fact);
    assert!(
        moved
            .check_mutex_use_input_return(&input, receiver, &resources)
            .is_err()
    );
    assert!(
        moved
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_err()
    );
    let returned = moved
        .apply(
            &moved
                .transfer(input.usage.0.share, receiver, holder)
                .unwrap(),
        )
        .unwrap();
    assert!(
        returned
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_ok()
    );
    let (child_state, child) = returned
        .reborrow_mutex_use(input.usage, holder, holder)
        .unwrap();
    let child_fact = child_state.mutex_use_resource(child.usage, holder).unwrap();
    let forged_input = MutexUseContractInput {
        holder,
        usage: child.usage,
    };
    assert!(
        child_state
            .check_mutex_use_input_return(
                &forged_input,
                holder,
                &ResourceContext::new().unchecked_with_fact(child_fact)
            )
            .is_err()
    );
}

#[test]
fn mutex_contract_input_return_requires_unsplit_unit_ownership() {
    let (ledger, holder, input, _) = abstract_mutex_input();
    let fact = ledger.mutex_use_resource(input.usage, holder).unwrap();
    for invalid in [
        ResourceFact::View(fact.resource().clone()),
        ResourceFact::Own(fact.resource().clone(), Box::new(MachineTerm::constant(0))),
        ResourceFact::Own(fact.resource().clone(), Box::new(MachineTerm::constant(2))),
    ] {
        assert!(
            ledger
                .check_mutex_use_input_return(
                    &input,
                    holder,
                    &ResourceContext::new().unchecked_with_fact(invalid)
                )
                .is_err()
        );
    }
    let resources = ResourceContext::new().unchecked_with_fact(fact);
    let (transition, left, right) = ledger
        .split(input.usage.0.share, holder, holder, holder)
        .unwrap();
    let split = ledger.apply(&transition).unwrap();
    assert!(
        split
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_err()
    );
    let left_usage = MutexUseBinding(LoanAuthorityBinding {
        share: left,
        ..input.usage.0
    });
    let left_fact = split.mutex_use_resource(left_usage, holder).unwrap();
    let forged = MutexUseContractInput {
        holder,
        usage: left_usage,
    };
    assert!(
        split
            .check_mutex_use_input_return(
                &forged,
                holder,
                &ResourceContext::new().unchecked_with_fact(left_fact)
            )
            .is_err()
    );
    let joined = split
        .apply(&split.join(left, right, holder).unwrap())
        .unwrap();
    assert!(
        joined
            .check_mutex_use_input_return(&input, holder, &resources)
            .is_ok()
    );
    assert!(joined.invariant_holds());
}

#[test]
fn mutex_contract_input_evidence_checks_anchor_freshness_and_predecessor() {
    let ledger = LoanLedger::new();
    let holder = ledger.fresh_participant().unwrap();
    let arena = ledger.storage.data.arena;
    let mut evidence = LoanTransitionEvidence::BorrowedMutexUseRoot {
        holder,
        support: backing(&owned("input")),
        mutex: Pointer::symbolic(Variable(4321)),
        protected: None,
        initialization: super::super::mutexes::MutexInitializationId::fresh().unwrap(),
        scope: LoanScopeId {
            arena,
            ordinal: ledger.storage.data.next_scope,
        },
        loan: LoanId {
            arena,
            ordinal: ledger.storage.data.next_loan,
        },
        root: LoanShareId {
            arena,
            ordinal: ledger.storage.data.next_share,
        },
    };
    let checked = ledger.issue(evidence.clone()).unwrap();
    let successor = ledger.apply(&checked).unwrap();
    assert!(successor.invariant_holds());
    assert!(successor.apply(&checked).is_err());
    assert!(successor.issue(evidence.clone()).is_err());
    let LoanTransitionEvidence::BorrowedMutexUseRoot { support, .. } = &mut evidence else {
        unreachable!()
    };
    *support = ResourceOccurrenceId::default();
    assert_eq!(ledger.issue(evidence), Err(LoanRefusal::MissingBacking));
    let foreign = LoanLedger::new().fresh_participant().unwrap();
    assert!(
        ledger
            .borrowed_mutex_use_input(
                foreign,
                backing(&owned("input")),
                Pointer::symbolic(Variable(4321))
            )
            .is_err()
    );
}

#[test]
fn mutex_use_reborrow_pins_parent_and_guard_blocks_return_across_participants() {
    let (ledger, owner, worker) = participants();
    let helper = ledger.fresh_participant().unwrap();
    let live = mutex_owner(Some(1));
    let (ledger, root) = ledger
        .lend_mutex_use(owner, worker, backing(&live), live.clone())
        .unwrap();
    let (ledger, child) = ledger
        .reborrow_mutex_use(root.usage, worker, helper)
        .unwrap();
    assert!(ledger.hold_mutex_use(root.usage, &live, worker).is_err());
    assert!(
        ledger
            .reborrow_mutex_use(root.usage, worker, helper)
            .is_err()
    );
    assert!(ledger.recover_mutex_use(&root, owner).is_err());
    assert!(ledger.recover_mutex_use(&child, helper).is_err());
    assert!(ledger.recover(child.loan, helper).is_err());
    assert!(ledger.permitted_descriptions(child.loan).is_empty());
    assert!(!ledger.has_active_memory_loans());
    let (ledger, hold) = ledger.hold_mutex_use(child.usage, &live, helper).unwrap();
    let ledger = ledger
        .apply(
            &ledger
                .transfer(child.usage.0.share, helper, worker)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(
        ledger.end_mutex_reborrow(&child, worker),
        Err(LoanRefusal::ActiveDependency)
    );
    assert!(ledger.release(hold, worker).is_err());
    let ledger = ledger.release(hold, helper).unwrap();
    let ledger = ledger.end_mutex_reborrow(&child, worker).unwrap();
    assert!(ledger.end_mutex_reborrow(&child, worker).is_err());
    assert!(ledger.hold_mutex_use(child.usage, &live, worker).is_err());
    assert!(ledger.hold_mutex_use(root.usage, &live, worker).is_ok());
    let ledger = ledger
        .apply(&ledger.transfer(root.usage.0.share, worker, owner).unwrap())
        .unwrap();
    let (ledger, recovered) = ledger.recover_mutex_use(&root, owner).unwrap();
    assert_eq!(recovered, live);
    assert!(ledger.invariant_holds());
}

#[test]
fn mutex_use_reborrow_preserves_sibling_share_and_initialization() {
    let (ledger, owner, helper) = participants();
    let live = mutex_owner(Some(1));
    let (ledger, root) = ledger
        .lend_mutex_use(owner, owner, backing(&live), live.clone())
        .unwrap();
    let (split, left, right) = ledger
        .split(root.usage.0.share, owner, owner, owner)
        .unwrap();
    let ledger = ledger.apply(&split).unwrap();
    let left_use = MutexUseBinding(LoanAuthorityBinding {
        share: left,
        ..root.usage.0
    });
    let right_use = MutexUseBinding(LoanAuthorityBinding {
        share: right,
        ..root.usage.0
    });
    let (ledger, child) = ledger.reborrow_mutex_use(left_use, owner, helper).unwrap();
    assert!(ledger.hold_mutex_use(left_use, &live, owner).is_err());
    assert!(ledger.hold_mutex_use(right_use, &live, owner).is_ok());
    assert!(
        ledger
            .hold_mutex_use(child.usage, &mutex_owner(Some(2)), helper)
            .is_err()
    );
    assert!(ledger.hold_mutex_use(child.usage, &live, helper).is_ok());
    assert_eq!(
        ledger
            .storage
            .data
            .loans
            .get(&child.loan)
            .unwrap()
            .mutex_root,
        Some(root.loan)
    );
    assert!(
        ledger
            .storage
            .data
            .loans
            .get(&child.loan)
            .unwrap()
            .escrow
            .is_none()
    );
    assert!(ledger.end_mutex_reborrow(&root, owner).is_err());
    let forged = MutexUseLoan {
        scope: root.scope,
        ..child.clone()
    };
    assert!(ledger.end_mutex_reborrow(&forged, helper).is_err());
    assert!(ledger.invariant_holds());
}

#[test]
fn mutex_use_reborrow_rejects_forged_parent_and_stale_transition() {
    let (ledger, owner, helper) = participants();
    let live = mutex_owner(Some(1));
    let (ledger, root) = ledger
        .lend_mutex_use(owner, owner, backing(&live), live.clone())
        .unwrap();
    let (next, child) = ledger
        .reborrow_mutex_use(root.usage, owner, helper)
        .unwrap();
    let evidence = LoanTransitionEvidence::Reborrow {
        parent: ReborrowBinding::MutexUse(root.usage),
        lender: owner,
        borrower: helper,
        scope: child.scope,
        loan: child.loan,
        root: child.usage.0.share,
    };
    let transition = ledger.issue(evidence.clone()).unwrap();
    assert_eq!(next.apply(&transition), Err(LoanRefusal::StalePredecessor));
    let mut forged = evidence;
    let LoanTransitionEvidence::Reborrow { parent, .. } = &mut forged else {
        panic!("reborrow")
    };
    *parent = ReborrowBinding::MutexUse(MutexUseBinding(LoanAuthorityBinding {
        support: ResourceOccurrenceId::default(),
        ..root.usage.0
    }));
    assert!(ledger.issue(forged).is_err());
    assert!(
        ledger
            .reborrow_mutex_use(root.usage, helper, owner)
            .is_err()
    );
    let (foreign, foreign_owner, _) = participants();
    assert!(
        foreign
            .reborrow_mutex_use(root.usage, foreign_owner, foreign_owner)
            .is_err()
    );
    let fact = owned("ordinary-token");
    let opening = ledger.lend(owner, owner, backing(&fact), fact).unwrap();
    let ordinary = ledger.apply(&opening.transition).unwrap();
    let fabricated = MutexUseBinding(LoanAuthorityBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: opening.description.support(),
    });
    assert!(
        ordinary
            .reborrow_mutex_use(fabricated, owner, helper)
            .is_err()
    );
}

#[test]
fn mutex_use_lending_never_authorizes_a_stable_view() {
    let (ledger, owner, reader) = participants();
    let live = mutex_owner(Some(1));
    let support = backing(&live);
    assert_eq!(
        ledger.lend(owner, reader, support, live.clone()),
        Err(LoanRefusal::UnsupportedResource)
    );
    let (ledger, loan) = ledger
        .lend_mutex_use(owner, reader, support, live.clone())
        .unwrap();
    assert!(!ledger.has_active_memory_loans());
    assert!(ledger.permitted_descriptions(loan.loan).is_empty());
    assert!(
        ledger
            .describe_view(
                loan.loan,
                ResourceFact::View(live.resource().clone()),
                &PureFactContext::new()
            )
            .is_err()
    );
    assert!(
        ledger
            .describe_view(loan.loan, memory(0, 1, false), &PureFactContext::new())
            .is_err()
    );
    assert_eq!(
        ledger.hold_mutex_use(loan.usage, &mutex_owner(Some(2)), reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert_eq!(
        ledger.hold_mutex_use(loan.usage, &mutex_owner(None), reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert!(
        ledger
            .reborrow(
                LoanViewBinding {
                    loan: loan.loan,
                    scope: loan.scope,
                    share: loan.usage.0.share,
                    support,
                    viewed: ResourceFact::View(live.resource().clone()),
                    hold: None,
                },
                reader,
                owner
            )
            .is_err()
    );
    assert!(ledger.invariant_holds());
}

#[test]
fn mutex_use_shares_and_guard_holds_must_all_return_before_recovery() {
    let (ledger, owner, worker) = participants();
    let live = mutex_owner(Some(1));
    let support = backing(&live);
    let (ledger, loan) = ledger
        .lend_mutex_use(owner, owner, support, live.clone())
        .unwrap();
    let (split, left, right) = ledger
        .split(loan.usage.0.share, owner, owner, worker)
        .unwrap();
    let ledger = ledger.apply(&split).unwrap();
    let worker_use = MutexUseBinding(LoanAuthorityBinding {
        share: right,
        ..loan.usage.0
    });
    assert!(ledger.recover_mutex_use(&loan, owner).is_err());
    assert!(ledger.hold_mutex_use(loan.usage, &live, owner).is_err());
    let (ledger, hold) = ledger.hold_mutex_use(worker_use, &live, worker).unwrap();
    let ledger = ledger
        .apply(&ledger.transfer(right, worker, owner).unwrap())
        .unwrap();
    let ledger = ledger
        .apply(&ledger.join(left, right, owner).unwrap())
        .unwrap();
    assert_eq!(
        ledger.recover_mutex_use(&loan, owner),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(ledger.release(hold, owner), Err(LoanRefusal::WrongHolder));
    let ledger = ledger.release(hold, worker).unwrap();
    let (ledger, recovered) = ledger.recover_mutex_use(&loan, owner).unwrap();
    assert_eq!(recovered, live);
    assert!(ledger.recover_mutex_use(&loan, owner).is_err());
    assert!(ledger.hold_mutex_use(worker_use, &live, worker).is_err());
    assert!(ledger.invariant_holds());
}

#[test]
fn mutex_use_rejects_invented_owners_receipts_and_certificates() {
    let (ledger, owner, reader) = participants();
    for escrow in [
        memory(0, 1, true),
        owned("token"),
        ResourceFact::Own(
            mutex_owner(Some(1)).resource().clone(),
            Box::new(2u32.into()),
        ),
        ResourceFact::View(mutex_owner(Some(1)).resource().clone()),
    ] {
        assert_eq!(
            ledger.lend_mutex_use(owner, reader, backing(&mutex_owner(Some(1))), escrow),
            Err(LoanRefusal::UnsupportedResource)
        );
    }
    let live = mutex_owner(Some(1));
    assert_eq!(
        ledger.lend_mutex_use(owner, reader, ResourceOccurrenceId::default(), live.clone()),
        Err(LoanRefusal::MissingBacking)
    );
    let (ledger, first) = ledger
        .lend_mutex_use(owner, owner, backing(&live), live.clone())
        .unwrap();
    let (ledger, second) = ledger
        .lend_mutex_use(owner, owner, backing(&live), live.clone())
        .unwrap();
    let forged = MutexUseLoan {
        scope: first.scope,
        loan: second.loan,
        usage: first.usage,
    };
    assert_eq!(
        ledger.recover_mutex_use(&forged, owner),
        Err(LoanRefusal::MissingLoanBinding)
    );
    let token = owned("token");
    let opening = ledger.lend(owner, owner, backing(&token), token).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let fake_use = MutexUseBinding(LoanAuthorityBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: opening.description.support(),
    });
    assert_eq!(
        ledger.hold_mutex_use(fake_use, &live, owner),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert!(
        ledger
            .recover_mutex_use(
                &MutexUseLoan {
                    scope: opening.scope,
                    loan: opening.loan,
                    usage: fake_use
                },
                owner
            )
            .is_err()
    );
    // A hostile certificate cannot replace lifetime ownership with a
    // view, even if it also substitutes its structural seal.
    let mut invalid = opening.transition;
    let LoanTransitionEvidence::Lend { escrow, .. } = &mut invalid.evidence else {
        panic!("lend")
    };
    *escrow = ResourceFact::View(mutex_owner(None).resource().clone());
    invalid.checked_evidence = invalid.evidence.clone();
    assert_eq!(
        ledger.apply_evidence(&invalid.evidence),
        Err(LoanRefusal::NotOwnership)
    );
}

#[test]
fn lifetime_hold_needs_possession_but_grants_no_read_or_recovery_authority() {
    let (ledger, owner, reader) = participants();
    let fact = owned("lifetime");
    let support = backing(&fact);
    let opening = ledger.lend(owner, reader, support, fact.clone()).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let authority = LoanAuthorityBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
    };
    let invalid_view = LoanViewBinding {
        loan: authority.loan,
        scope: authority.scope,
        share: authority.share,
        support,
        viewed: memory(0, 1, false),
        hold: None,
    };
    assert_eq!(
        ledger.hold(&invalid_view, reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
    let (held, hold, certificate) = ledger
        .hold_authority_with_transition(authority, reader)
        .unwrap();
    assert_eq!(ledger.apply(&certificate).unwrap(), held);
    assert!(!held.has_active_memory_loans());
    assert_eq!(
        held.permitted_descriptions(opening.loan),
        ledger.permitted_descriptions(opening.loan)
    );
    assert_eq!(
        held.validate_view_binding(invalid_view, reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert_eq!(
        held.recover(opening.loan, reader),
        Err(LoanRefusal::InvalidEvidence)
    );
    assert_eq!(
        held.recover(opening.loan, owner),
        Err(LoanRefusal::ScopeStillActive)
    );
    let moved = held
        .apply(&held.transfer(opening.root_share, reader, owner).unwrap())
        .unwrap();
    assert_eq!(
        moved.end(opening.scope, owner),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(
        moved.hold_authority_with_transition(authority, reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
    let released = moved.release(hold, reader).unwrap();
    let ended = released
        .apply(&released.end(opening.scope, owner).unwrap())
        .unwrap();
    assert_eq!(
        ended.hold_authority_with_transition(authority, owner),
        Err(LoanRefusal::MissingLoanBinding)
    );
    let (recover, recovered, _) = ended.recover(opening.loan, owner).unwrap();
    assert_eq!(recovered, fact);
    assert!(ended.apply(&recover).unwrap().invariant_holds());
}

#[test]
fn lifetime_hold_rechecks_split_reborrow_and_exact_occurrence() {
    let (ledger, owner, reader) = participants();
    let fact = owned("same-description");
    let support = backing(&fact);
    let opening = ledger.lend(owner, reader, support, fact.clone()).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let authority = LoanAuthorityBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
    };
    let other = ledger.lend(owner, reader, backing(&fact), fact).unwrap();
    let ledger = ledger.apply(&other.transition).unwrap();
    for forged in [
        LoanAuthorityBinding {
            loan: other.loan,
            ..authority
        },
        LoanAuthorityBinding {
            scope: other.scope,
            ..authority
        },
        LoanAuthorityBinding {
            share: other.root_share,
            ..authority
        },
        LoanAuthorityBinding {
            support: other.description.support(),
            ..authority
        },
    ] {
        assert_eq!(
            ledger.hold_authority_with_transition(forged, reader),
            Err(LoanRefusal::MissingLoanBinding)
        );
    }
    let (split, left, right) = ledger
        .split(authority.share, reader, reader, owner)
        .unwrap();
    let ledger = ledger.apply(&split).unwrap();
    assert_eq!(
        ledger.hold_authority_with_transition(authority, reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
    let left_authority = LoanAuthorityBinding {
        share: left,
        ..authority
    };
    assert!(
        ledger
            .hold_authority_with_transition(left_authority, reader)
            .is_ok()
    );
    assert_eq!(
        ledger.hold_authority_with_transition(
            LoanAuthorityBinding {
                share: right,
                ..authority
            },
            reader
        ),
        Err(LoanRefusal::MissingLoanBinding)
    );
    let child = ledger
        .reborrow(
            LoanViewBinding {
                loan: authority.loan,
                scope: authority.scope,
                share: left,
                support,
                viewed: opening.description.viewed().clone(),
                hold: None,
            },
            reader,
            owner,
        )
        .unwrap();
    let ledger = ledger.apply(&child.transition).unwrap();
    assert_eq!(
        ledger.hold_authority_with_transition(left_authority, reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
    let child_authority = LoanAuthorityBinding {
        loan: child.loan,
        scope: child.scope,
        share: child.root_share,
        support,
    };
    let (held, hold, _) = ledger
        .hold_authority_with_transition(child_authority, owner)
        .unwrap();
    let held = held
        .apply(&held.transfer(child.root_share, owner, reader).unwrap())
        .unwrap();
    assert_eq!(
        held.end(child.scope, reader),
        Err(LoanRefusal::ActiveDependency)
    );
    let released = held.release(hold, owner).unwrap();
    let ended = released
        .apply(&released.end(child.scope, reader).unwrap())
        .unwrap();
    assert!(
        ended
            .hold_authority_with_transition(left_authority, reader)
            .is_ok()
    );
    assert!(ended.invariant_holds());
}

#[test]
fn lifetime_hold_certificate_cannot_substitute_a_different_share() {
    let (ledger, owner, reader) = participants();
    let fact = owned("lifetime");
    let support = backing(&fact);
    let opening = ledger.lend(owner, reader, support, fact).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let binding = LoanAuthorityBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
    };
    let (held, _, mut certificate) = ledger
        .hold_authority_with_transition(binding, reader)
        .unwrap();
    assert_eq!(held.apply(&certificate), Err(LoanRefusal::StalePredecessor));
    let LoanTransitionEvidence::Hold { binding, .. } = &mut certificate.evidence else {
        panic!("hold certificate")
    };
    binding.support = ResourceOccurrenceId::default();
    assert_eq!(
        ledger.apply(&certificate),
        Err(LoanRefusal::InvalidEvidence)
    );
    // Even rewriting the structural seal cannot bypass the transition's
    // own possession check when the checker rechecks it.
    certificate.checked_evidence = certificate.evidence.clone();
    assert_eq!(
        ledger.apply(&certificate),
        Err(LoanRefusal::MissingLoanBinding)
    );
}

/// A hold placed by a folded borrowing composite keeps the loan's scope
/// from ending, and therefore the owner from being recovered, until it is
/// released by the participant that placed it. The hold changes ledger
/// identity but mints no share or recovery right (escaping borrows in
/// docs/internals/stable-views.md).
#[test]
fn a_hold_blocks_ending_the_scope_and_changes_identity() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let escrow = ResourceFact::own_memory(parameter_range(31, 0, 1, 4));
    let support = backing(&escrow);
    let opening = ledger.lend(owner, reader, support, escrow.clone()).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: escrow.core().unwrap(),
        hold: None,
    };
    let (held, hold, hold_transition) = ledger
        .hold_with_transition(&binding, reader)
        .expect("the borrower may hold");
    assert_eq!(
        ledger.apply(&hold_transition).expect("hold recheck"),
        held,
        "reapplying the checked hold must reproduce its exact identity"
    );
    assert!(held.invariant_holds());
    assert_ne!(held, ledger, "placing a hold changes the ledger identity");
    assert_eq!(held.held_scope(hold), Some(opening.scope));
    // No share or recovery right is minted: the held binding still
    // authorizes exactly the same description.
    assert!(held.permits_view(
        reader,
        &StableViewDescription {
            loan: opening.loan,
            support,
            viewed: escrow.core().unwrap(),
        },
        opening.root_share,
        &assumptions,
    ));
    let transfer = held.transfer(opening.root_share, reader, owner).unwrap();
    let held = held.apply(&transfer).unwrap();
    assert_eq!(
        held.end(opening.scope, owner),
        Err(LoanRefusal::ActiveDependency),
        "a held scope cannot end"
    );
    assert_eq!(
        held.release(hold, owner),
        Err(LoanRefusal::WrongHolder),
        "only the participant that placed the hold releases it"
    );
    let (released, release_transition) =
        held.release_with_transition(hold, reader).expect("release");
    assert_eq!(
        held.apply(&release_transition).expect("release recheck"),
        released,
        "reapplying the checked release must reproduce its exact identity"
    );
    assert_ne!(
        released, held,
        "releasing a hold changes the ledger identity"
    );
    assert!(released.invariant_holds());
    assert_eq!(released.held_scope(hold), None);
    assert_eq!(
        released.release(hold, reader),
        Err(LoanRefusal::MissingScope),
        "a hold is released once"
    );
    let end = released
        .end(opening.scope, owner)
        .expect("an unheld scope ends");
    let released = released.apply(&end).unwrap();
    let (recover, recovered_escrow, _) = released.recover(opening.loan, owner).unwrap();
    let released = released.apply(&recover).unwrap();
    assert_eq!(recovered_escrow, escrow);
    assert!(released.invariant_holds());
}

/// A borrowing fold's ledger change is accepted only as the exact hold
/// its folded head names: the placer, the authority and the hold
/// identity must all agree, and the transition must start at the exact
/// input ledger.
#[test]
fn a_borrowing_fold_hold_is_exactly_the_hold_its_head_carries() {
    let (ledger, holder, other) = participants();
    let viewed = ResourceFact::view_memory(parameter_range(32, 0, 1, 4));
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .borrowed_contract_input(holder, support, viewed.clone(), None)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed,
        hold: None,
    };
    let (held, hold, transition) = ledger.hold_with_transition(&binding, holder).unwrap();
    let carried = LoanViewBinding {
        hold: Some(hold),
        ..binding.clone()
    };
    assert_eq!(
        ledger.apply_borrowing_fold_hold(&transition, &carried, holder),
        Ok(held.clone())
    );
    assert_eq!(
        ledger.apply_borrowing_fold_hold(&transition, &binding, holder),
        Err(LoanRefusal::InvalidEvidence),
        "the head must carry the hold"
    );
    assert_eq!(
        ledger.apply_borrowing_fold_hold(&transition, &carried, other),
        Err(LoanRefusal::InvalidEvidence),
        "the hold must be the folding participant's"
    );
    let elsewhere = LoanViewBinding {
        support: ResourceOccurrenceId::default(),
        ..carried.clone()
    };
    assert_eq!(
        ledger.apply_borrowing_fold_hold(&transition, &elsewhere, holder),
        Err(LoanRefusal::InvalidEvidence),
        "the hold must be on the head's loan authority"
    );
    assert_eq!(
        held.apply_borrowing_fold_hold(&transition, &carried, holder),
        Err(LoanRefusal::StalePredecessor),
        "the hold applies only to its exact input ledger"
    );
}

/// A hold requires a live binding of its placer: a stale or foreign
/// binding is refused, and a contract-input root (which never ends) can
/// still be held so the fold inside a modular proof is recorded.
#[test]
fn a_hold_needs_a_live_binding_and_may_rest_on_a_contract_input_root() {
    let (ledger, holder, other) = participants();
    let viewed = ResourceFact::view_memory(parameter_range(32, 0, 1, 4));
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .borrowed_contract_input(holder, support, viewed.clone(), None)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed,
        hold: None,
    };
    assert_eq!(
        ledger.hold(&binding, other),
        Err(LoanRefusal::MissingLoanBinding),
        "the share is not held by `other`"
    );
    let (held, hold) = ledger.hold(&binding, holder).unwrap();
    assert!(held.invariant_holds());
    assert_eq!(held.held_scope(hold), Some(opening.scope));
    assert_ne!(held, ledger, "contract-input holds also change identity");
}

/// A composite loan is a memory loan whether or not its one-level
/// frontier enumerated any bytes: the head is memory.
#[test]
fn composite_lend_counts_as_a_memory_loan_without_byte_backing() {
    let (ledger, owner, reader) = participants();
    let head = ResourceFact::own(Resource::Composite {
        name: "box".to_string(),
        arguments: Vec::new().into(),
    });
    let piece = owned("box_token");
    let support = backing(&head);
    let backing = CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![piece])
        .expect("a token-only frontier is a checked expansion");
    let opening = ledger
        .lend_composite(owner, reader, support, head, backing)
        .expect("composite lend");
    let ledger = ledger.apply(&opening.transition).unwrap();
    assert!(ledger.has_active_memory_loans());
    assert!(ledger.invariant_holds());
    let transfer = ledger.transfer(opening.root_share, reader, owner).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let end = ledger.end(opening.scope, owner).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    assert!(!ledger.has_active_memory_loans());
    assert!(ledger.invariant_holds());
}

#[test]
fn nested_reborrow_restores_a_borrowed_contract_input_root() {
    let (ledger, holder, reader) = participants();
    let assumptions = PureFactContext::new();
    let viewed = memory(0, 4, false);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .borrowed_contract_input(holder, support, viewed.clone(), None)
        .expect("checked contract input");
    let ledger = ledger.apply(&opening.transition).expect("apply input root");
    let parent = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed,
        hold: None,
    };
    let child = ledger
        .reborrow(parent, holder, reader)
        .expect("checked child reborrow");
    let ledger = ledger.apply(&child.transition).expect("apply child");
    assert!(!ledger.permits_view(
        holder,
        &opening.description,
        opening.root_share,
        &assumptions,
    ));
    let transfer = ledger
        .transfer(child.root_share, reader, holder)
        .expect("return child share");
    let ledger = ledger.apply(&transfer).expect("apply return");
    let end = ledger
        .end(child.scope, holder)
        .expect("close child scope only");
    let ledger = ledger.apply(&end).expect("apply child close");

    assert!(ledger.invariant_holds());
    assert!(ledger.permits_view(
        holder,
        &opening.description,
        opening.root_share,
        &assumptions,
    ));
    assert_eq!(
        ledger.recover(child.loan, holder),
        Err(LoanRefusal::InvalidEvidence)
    );
}

#[test]
fn checked_two_reader_lifecycle_recovers_exact_escrow_once() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let escrow = owned("cell");
    let opening = lend_test(&ledger, owner, owner, escrow.clone());
    let ledger = ledger.apply(&opening.transition).unwrap();
    let (split, left, right) = ledger
        .split(opening.root_share, owner, owner, reader)
        .unwrap();
    let ledger = ledger.apply(&split).unwrap();
    assert!(ledger.permits_view(owner, &opening.description, left, &assumptions));
    assert!(ledger.permits_view(reader, &opening.description, right, &assumptions));
    assert_eq!(
        ledger.end(opening.scope, owner),
        Err(LoanRefusal::ShareStillSplit)
    );
    let transfer = ledger.transfer(right, reader, owner).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let join = ledger.join(left, right, owner).unwrap();
    let ledger = ledger.apply(&join).unwrap();
    let end = ledger.end(opening.scope, owner).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    let lifetime = ledger
        .end(opening.scope, owner)
        .expect_err("an ended scope cannot be ended again");
    assert_eq!(
        lifetime
            .diagnostic(LoanRefusalOperation::Transition)
            .category(),
        LoanRefusalCategory::Lifetime
    );
    assert!(!ledger.permits_view(
        owner,
        &opening.description,
        opening.root_share,
        &assumptions
    ));
    let (recover, recovered, support) = ledger.recover(opening.loan, owner).unwrap();
    assert_eq!(recovered, escrow);
    assert_eq!(support, opening.description.support());
    let ledger = ledger.apply(&recover).unwrap();
    assert!(ledger.invariant_holds());
    let duplicate = ledger
        .recover(opening.loan, owner)
        .expect_err("a loan cannot be recovered twice");
    assert_eq!(
        duplicate
            .diagnostic(LoanRefusalOperation::Recovery)
            .category(),
        LoanRefusalCategory::Recovery
    );
}

#[test]
fn shared_reader_recovery_rejects_wrong_sibling_reuse_and_stale_branch() {
    let (ledger, owner, first_reader) = participants();
    let second_reader = ledger.fresh_participant().unwrap();
    let opening = lend_test(&ledger, owner, owner, owned("shared_cell"));
    let ledger = ledger.apply(&opening.transition).unwrap();

    // Splitting the parent's remaining share for a second reader makes
    // the workers' shares cousins, not siblings of one another.
    let (split_first, parent_share, first_share) = ledger
        .split(opening.root_share, owner, owner, first_reader)
        .unwrap();
    let ledger = ledger.apply(&split_first).unwrap();
    let (split_second, retained_share, second_share) = ledger
        .split(parent_share, owner, owner, second_reader)
        .unwrap();
    let ledger = ledger.apply(&split_second).unwrap();
    assert_eq!(
        ledger.join(retained_share, first_share, owner),
        Err(LoanRefusal::WrongHolder)
    );

    let return_first = ledger.transfer(first_share, first_reader, owner).unwrap();
    let after_first_return = ledger.apply(&return_first).unwrap();
    assert_eq!(
        after_first_return.join(first_share, retained_share, owner),
        Err(LoanRefusal::NotSiblings),
        "a returned worker share cannot join the other branch's retained share"
    );
    assert_eq!(
        after_first_return
            .join_available_share_ancestors(first_share, owner)
            .unwrap()
            .2
            .len(),
        0,
        "the other worker still pins the sibling subtree"
    );
    assert_eq!(
        after_first_return.end(opening.scope, owner),
        Err(LoanRefusal::ShareStillSplit)
    );

    let return_second = after_first_return
        .transfer(second_share, second_reader, owner)
        .unwrap();
    let after_both_returns = after_first_return.apply(&return_second).unwrap();
    let (recombined, root, joins) = after_both_returns
        .join_available_share_ancestors(second_share, owner)
        .unwrap();
    assert_eq!(root, opening.root_share);
    assert_eq!(joins.len(), 2);
    assert_eq!(
        after_first_return.apply(&joins[0]),
        Err(LoanRefusal::StalePredecessor),
        "a join certificate cannot be transplanted before the second return"
    );
    assert_eq!(
        recombined.apply(&joins[0]),
        Err(LoanRefusal::StalePredecessor),
        "a consumed sibling join cannot be used twice"
    );
    assert_eq!(
        recombined.join(first_share, second_share, owner),
        Err(LoanRefusal::WrongHolder),
        "consumed shares cannot be joined again"
    );
    let mut forged = joins[0].clone();
    if let LoanTransitionEvidence::Join { right, .. } = &mut forged.evidence {
        *right = first_share;
    } else {
        panic!("expected a checked sibling join");
    }
    assert_eq!(
        after_both_returns.apply(&forged),
        Err(LoanRefusal::InvalidEvidence),
        "a changed sibling identity invalidates the checked payload"
    );
    assert!(recombined.invariant_holds());
    let end = recombined.end(opening.scope, owner).unwrap();
    let ended = recombined.apply(&end).unwrap();
    let (recover, _, _) = ended.recover(opening.loan, owner).unwrap();
    assert!(ended.apply(&recover).unwrap().invariant_holds());
}

/// D2 law 4: a description outlives its authority, and D2 law 5: a
/// reused resource term is not a reused identity. The first loan over a
/// cell ends and is recovered, then a fresh loan starts over the very
/// same support occurrence and the very same resource term. One
/// participant lends to itself throughout, so the old binding's share is
/// never handed away: only scope and loan identity separate the two, and
/// the old description, binding, and reborrow are all refused while the
/// new ones are accepted (R04's fresh-scope case; docs/internals/stable-views.md).
#[test]
fn an_old_descriptor_is_refused_after_a_fresh_scope_over_the_same_resource() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let escrow = owned("cell");
    let support = backing(&escrow);
    let first = ledger
        .lend(owner, owner, support, escrow.clone())
        .expect("a first loan over the cell");
    let ledger = ledger.apply(&first.transition).unwrap();
    let old_binding = LoanViewBinding {
        loan: first.loan,
        scope: first.scope,
        share: first.root_share,
        support,
        viewed: first.description.viewed().clone(),
        hold: None,
    };
    assert!(ledger.permits_view(owner, &first.description, first.root_share, &assumptions));
    assert_eq!(
        ledger.validate_view_binding(old_binding.clone(), owner),
        Ok(())
    );
    ledger
        .reborrow(old_binding.clone(), owner, reader)
        .expect("the live binding reborrows");

    // Close the first loan and recover its escrow. The share stays with
    // the same holder, so nothing but scope liveness changes.
    let end = ledger.end(first.scope, owner).unwrap();
    let ledger = ledger.apply(&end).unwrap();
    let (recover, recovered, recovered_support) = ledger.recover(first.loan, owner).unwrap();
    assert_eq!(recovered, escrow);
    assert_eq!(recovered_support, support);
    let ledger = ledger.apply(&recover).unwrap();

    // A fresh loan over the same support occurrence and resource term.
    let second = ledger
        .lend(owner, owner, support, escrow)
        .expect("a fresh loan over the same cell");
    let ledger = ledger.apply(&second.transition).unwrap();
    assert!(ledger.invariant_holds());
    assert_ne!(first.loan, second.loan);
    assert_ne!(first.scope, second.scope);
    assert_eq!(first.description.viewed(), second.description.viewed());

    // The new scope authorizes reading, binding, and reborrowing.
    let new_binding = LoanViewBinding {
        loan: second.loan,
        scope: second.scope,
        share: second.root_share,
        support,
        viewed: second.description.viewed().clone(),
        hold: None,
    };
    assert!(ledger.permits_view(owner, &second.description, second.root_share, &assumptions));
    assert_eq!(
        ledger.validate_view_binding(new_binding.clone(), owner),
        Ok(())
    );
    ledger
        .reborrow(new_binding, owner, reader)
        .expect("the live binding reborrows");

    // The old descriptor authorizes nothing, on any of the three routes.
    assert!(!ledger.permits_view(owner, &first.description, first.root_share, &assumptions));
    // Nor when paired with the new scope's live share: the description
    // still names the ended loan.
    assert!(!ledger.permits_view(owner, &first.description, second.root_share, &assumptions));
    assert_eq!(
        ledger.validate_view_binding(old_binding.clone(), owner),
        Err(LoanRefusal::MissingLoanBinding)
    );
    assert_eq!(
        ledger.reborrow(old_binding, owner, reader),
        Err(LoanRefusal::MissingLoanBinding)
    );
}

#[test]
fn transitions_are_bound_to_their_exact_predecessor() {
    let (ledger, owner, reader) = participants();
    let opening = lend_test(&ledger, owner, reader, owned("cell"));
    let advanced = ledger.apply(&opening.transition).unwrap();
    let stale = advanced
        .apply(&opening.transition)
        .expect_err("a transition cannot be applied twice");
    assert_eq!(
        stale
            .diagnostic(LoanRefusalOperation::Transition)
            .category(),
        LoanRefusalCategory::StalePredecessor
    );
    let unrelated = LoanLedger::new();
    let stale = unrelated
        .apply(&opening.transition)
        .expect_err("a transition cannot cross ledger histories");
    assert_eq!(
        stale
            .diagnostic(LoanRefusalOperation::Transition)
            .category(),
        LoanRefusalCategory::StalePredecessor
    );
}

#[test]
fn divergent_successors_have_distinct_state_identities() {
    let (ledger, owner, reader) = participants();
    let first = lend_test(&ledger, owner, reader, owned("first"));
    let second = lend_test(&ledger, owner, reader, owned("second"));
    let first = ledger.apply(&first.transition).unwrap();
    let second = ledger.apply(&second.transition).unwrap();
    assert_ne!(first, second);
    assert!(!first.shares_storage_with(&second));
}

#[test]
fn hostile_transition_payload_is_rechecked() {
    let (ledger, owner, reader) = participants();
    let mut opening = lend_test(&ledger, owner, reader, owned("cell"));
    let LoanTransitionEvidence::Lend { borrower, .. } = &mut opening.transition.evidence else {
        panic!("lend evidence")
    };
    *borrower = owner;
    let invalid = ledger
        .apply(&opening.transition)
        .expect_err("tampered participant evidence must be refused");
    assert_eq!(
        invalid
            .diagnostic(LoanRefusalOperation::Transition)
            .category(),
        LoanRefusalCategory::InvalidEvidence
    );
}

#[test]
fn runtime_mutex_evidence_requires_exact_predecessor_participant_and_successor() {
    let (ledger, holder, other) = participants();
    let owner = mutex_owner(Some(1));
    let (before, loan) = ledger
        .lend_mutex_use(holder, holder, backing(&owner), owner.clone())
        .unwrap();
    let (held, hold, transition) = before
        .hold_mutex_use_with_transition(loan.usage, &owner, holder)
        .unwrap();
    let evidence = CheckedLoanCallEvidence::runtime_mutex_transition(
        &before,
        holder,
        transition.clone(),
        &held,
    )
    .unwrap();
    assert!(
        evidence
            .recheck(&before, Some(holder), &before, Some(holder))
            .is_ok()
    );
    assert!(
        CheckedLoanCallEvidence::runtime_mutex_transition(
            &before,
            other,
            transition.clone(),
            &held
        )
        .is_err()
    );
    assert!(
        CheckedLoanCallEvidence::runtime_mutex_transition(
            &before,
            holder,
            transition.clone(),
            &before
        )
        .is_err()
    );
    assert!(
        CheckedLoanCallEvidence::runtime_mutex_transition(&held, holder, transition, &held)
            .is_err()
    );
    let (released, release) = held.release_with_transition(hold, holder).unwrap();
    assert!(
        CheckedLoanCallEvidence::runtime_mutex_transition(
            &held,
            holder,
            release.clone(),
            &released
        )
        .is_ok()
    );
    assert!(
        CheckedLoanCallEvidence::runtime_mutex_transition(&held, holder, release, &before).is_err()
    );
}

#[test]
fn checked_call_evidence_rejects_stale_or_swapped_recovery() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 4, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(0, 2, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let planned_ledger = plan.ledger.clone();
    let recovery = plan
        .clone()
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    let recovery_subject = recovery.diagnostic_subject();
    assert!(
        recovery_subject.loan_id().is_some()
            || recovery_subject.scope_id().is_some()
            || recovery_subject.share_id().is_some()
            || recovery_subject.support_id().is_some()
    );
    let evidence = CheckedLoanCallEvidence::new(
        plan,
        recovery.ledger.clone(),
        recovery.terminal_ledger.clone(),
        recovery.transitions.clone(),
        recovery.hold_base_ledger.clone(),
        recovery.hold_transitions.clone(),
    );
    assert!(
        evidence
            .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
            .is_ok()
    );

    let mut stale = evidence.clone();
    stale.recovery_transitions.reverse();
    let stale_error = stale
        .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
        .expect_err("reordered recovery must be refused");
    assert_eq!(
        stale_error
            .diagnostic(LoanRefusalOperation::Recovery)
            .category(),
        LoanRefusalCategory::StalePredecessor
    );

    let mut truncated = evidence.clone();
    truncated.recovery_transitions.pop();
    let truncated_error = truncated
        .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
        .expect_err("truncated recovery must be refused");
    assert_eq!(
        truncated_error
            .diagnostic(LoanRefusalOperation::Recovery)
            .category(),
        LoanRefusalCategory::Recovery
    );

    let unrelated = LoanLedger::new();
    let unrelated_error = evidence
        .recheck(&unrelated, Some(caller), &planned_ledger, Some(callee))
        .expect_err("a cross-call predecessor must be refused");
    assert_eq!(
        unrelated_error
            .diagnostic(LoanRefusalOperation::Recovery)
            .category(),
        LoanRefusalCategory::StalePredecessor
    );
}

#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn checked_evidence_sequence_scales_with_shared_immutable_history() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 4, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(0, 2, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let recovery = plan
        .clone()
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    let evidence = Arc::new(CheckedLoanCallEvidence::new(
        plan,
        recovery.ledger,
        recovery.terminal_ledger,
        recovery.transitions,
        recovery.hold_base_ledger,
        recovery.hold_transitions,
    ));
    let mut sequence = empty_checked_loan_evidence_sequence();
    let mut midpoint = None;
    for index in 0..2048 {
        let previous = sequence.clone();
        sequence = append_checked_loan_evidence(&sequence, Some(evidence.clone()));
        let CheckedLoanCallEvidenceSequenceNode::Append { prefix, .. } = &*sequence.node else {
            panic!("append must create a persistent node");
        };
        assert!(Arc::ptr_eq(prefix, &previous.node));
        if index == 1023 {
            midpoint = Some(sequence.clone());
        }
    }
    let midpoint = midpoint.unwrap();
    let suffix = sequence.suffix_since(&midpoint).unwrap();
    assert_eq!(suffix.len(), 1024);
    assert_eq!(concat_checked_loan_evidence(&midpoint, &suffix), sequence);
    let separately_built_equal_prefix = midpoint
        .to_vec()
        .into_iter()
        .fold(empty_checked_loan_evidence_sequence(), |rebuilt, item| {
            append_checked_loan_evidence(&rebuilt, Some(item))
        });
    assert_eq!(separately_built_equal_prefix, midpoint);
    assert!(
        sequence
            .suffix_since(&separately_built_equal_prefix)
            .is_none()
    );
    assert_eq!(sequence.len(), 2048);
    assert_eq!(sequence, sequence.clone());
    assert_eq!(sequence.to_vec().len(), 2048);

    let alternate_plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(1, 3, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let alternate_recovery = alternate_plan
        .clone()
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    let alternate_evidence = Arc::new(CheckedLoanCallEvidence::new(
        alternate_plan,
        alternate_recovery.ledger,
        alternate_recovery.terminal_ledger,
        alternate_recovery.transitions,
        alternate_recovery.hold_base_ledger,
        alternate_recovery.hold_transitions,
    ));
    let mut separately_built_different = empty_checked_loan_evidence_sequence();
    for _ in 0..2048 {
        separately_built_different = append_checked_loan_evidence(
            &separately_built_different,
            Some(alternate_evidence.clone()),
        );
    }
    assert_ne!(separately_built_different, sequence);
}

#[test]
fn checked_evidence_sequence_seals_each_appended_call_locally() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 4, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(0, 2, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let recovery = plan
        .clone()
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    let mut tampered = CheckedLoanCallEvidence::new(
        plan,
        recovery.ledger,
        recovery.terminal_ledger,
        recovery.transitions,
        recovery.hold_base_ledger,
        recovery.hold_transitions,
    );
    tampered.recovery_transitions.reverse();
    let sequence = append_checked_loan_evidence(
        &empty_checked_loan_evidence_sequence(),
        Some(Arc::new(tampered)),
    );
    assert!(!sequence.is_valid());
}

#[test]
fn states_share_storage_and_updates_do_not_mutate_predecessors() {
    let (ledger, owner, reader) = participants();
    let clone = ledger.clone();
    assert!(ledger.shares_storage_with(&clone));
    let opening = lend_test(&ledger, owner, reader, owned("cell"));
    let advanced = ledger.apply(&opening.transition).unwrap();
    assert!(!ledger.shares_storage_with(&advanced));
    assert!(ledger.storage.data.loans.is_empty());
    assert_eq!(advanced.storage.data.loans.len(), 1);
}

#[test]
fn nested_reborrow_must_rejoin_each_parent_before_scope_end() {
    let (ledger, owner, reader) = participants();
    let opening = lend_test(&ledger, owner, owner, owned("cell"));
    let ledger = ledger.apply(&opening.transition).unwrap();
    let (outer_split, retained, reborrowed) = ledger
        .split(opening.root_share, owner, owner, reader)
        .unwrap();
    let ledger = ledger.apply(&outer_split).unwrap();
    let (nested_split, nested_left, nested_right) =
        ledger.split(reborrowed, reader, reader, reader).unwrap();
    let ledger = ledger.apply(&nested_split).unwrap();
    assert_eq!(
        ledger.join(retained, reborrowed, owner),
        Err(LoanRefusal::WrongHolder)
    );
    let nested_join = ledger.join(nested_left, nested_right, reader).unwrap();
    let ledger = ledger.apply(&nested_join).unwrap();
    let return_child = ledger.transfer(reborrowed, reader, owner).unwrap();
    let ledger = ledger.apply(&return_child).unwrap();
    let outer_join = ledger.join(retained, reborrowed, owner).unwrap();
    let ledger = ledger.apply(&outer_join).unwrap();
    assert!(ledger.end(opening.scope, owner).is_ok());
    assert!(ledger.invariant_holds());
}

#[test]
fn owner_observation_is_not_a_stable_view_description() {
    let resources = crate::kernel::ResourceContext::new().unchecked_with_fact(owned("cell"));
    let fact = resources.facts()[0].clone();
    let (occurrence, _) = resources.unique_owned_occurrence_for_fact(&fact).unwrap();
    let observation = OwnedResourceObservation::new(occurrence, &fact).unwrap();
    assert_eq!(observation.support(), occurrence);
    assert_eq!(
        observation.viewed(),
        &ResourceFact::View(fact.resource().clone())
    );
    let (_ledger, _owner, _reader) = participants();
    // Only `lend` creates a `StableViewDescription`; an observation has
    // no loan or scope identity to transfer to another participant.
    assert!(observation.viewed().is_view());
}

#[test]
fn participants_and_scope_ids_cannot_cross_ledger_arenas() {
    let (first, first_owner, _) = participants();
    let (_second, second_owner, second_reader) = participants();
    let cell = owned("cell");
    assert_eq!(
        first.lend(second_owner, second_reader, backing(&cell), cell.clone()),
        Err(LoanRefusal::WrongArena)
    );
    let opening = lend_test(&first, first_owner, first_owner, cell);
    let first = first.apply(&opening.transition).unwrap();
    assert_eq!(
        first.transfer(opening.root_share, second_owner, first_owner),
        Err(LoanRefusal::WrongArena)
    );
}

#[test]
fn reborrow_rejects_a_borrower_from_another_ledger_arena() {
    let (ledger, owner, _) = participants();
    let (_foreign_ledger, _, foreign_reader) = participants();
    let escrow = memory(0, 4, true);
    let opening = ledger.lend(owner, owner, backing(&escrow), escrow).unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let parent = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: opening.description.support(),
        viewed: memory(0, 4, false),
        hold: None,
    };
    assert_eq!(
        ledger.reborrow(parent, owner, foreign_reader),
        Err(LoanRefusal::WrongArena)
    );
}

#[test]
fn first_loan_family_boundary_rejects_composites() {
    let (ledger, owner, reader) = participants();
    let composite = ResourceFact::own_composite("cell".to_string(), Vec::new());
    assert_eq!(
        ledger.lend(owner, reader, backing(&composite), composite),
        Err(LoanRefusal::UnsupportedResource)
    );
}

#[test]
fn local_ledger_updates_allocate_logarithmically() {
    for size in [16_usize, 32, 64, 128] {
        let (mut ledger, owner, reader) = participants();
        for index in 0..size {
            let cell = owned(&format!("cell_{index}"));
            let opening = ledger.lend(owner, reader, backing(&cell), cell).unwrap();
            ledger = ledger.apply(&opening.transition).unwrap();
        }
        let ancestor = ledger.clone();
        assert!(ledger.shares_storage_with(&ancestor));
        let before = crate::persistent::persistent_node_allocations();
        let target = owned("target");
        let opening = ledger
            .lend(owner, reader, backing(&target), target)
            .unwrap();
        let successor = ledger.apply(&opening.transition).unwrap();
        let allocations = crate::persistent::persistent_node_allocations() - before;
        let logarithmic_height = usize::BITS as usize - size.leading_zeros() as usize;
        let allocation_bound = 64 * logarithmic_height + 64;
        assert!(
            allocations <= allocation_bound,
            "size {size} loan update allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert_eq!(ancestor.storage.data.loans.len(), size);
        assert_eq!(successor.storage.data.loans.len(), size + 1);
    }
}

pub(super) fn checked(fact: ResourceFact) -> CheckedResourceFact {
    CheckedResourceFact {
        fact,
        role: ResourceTransferRole::Borrow,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    }
}

pub(super) fn memory(start: u32, end: u32, own: bool) -> ResourceFact {
    let range = crate::kernel::MemoryRange::new(
        crate::kernel::Pointer {
            block: "buffer".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        crate::kernel::MachineTerm::constant(start),
        crate::kernel::MachineTerm::constant(end),
    );
    if own {
        ResourceFact::own_memory(range)
    } else {
        ResourceFact::view_memory(range)
    }
}

/// A ledger holding one live view of `buffer[0..4]`, which is what the
/// write barrier is there to protect.
fn ledger_lending_the_first_four_elements() -> LoanLedger {
    let (ledger, holder, _) = participants();
    let viewed = memory(0, 4, false);
    let resources = ResourceContext::new().unchecked_with_fact(viewed.clone());
    let support = resources.occurrences_for_fact(&viewed)[0];
    let opening = ledger
        .borrowed_contract_input(holder, support, viewed, None)
        .expect("checked contract input");
    ledger.apply(&opening.transition).expect("apply input root")
}

fn range(start: u32, end: u32) -> MemoryRange {
    memory(start, end, true).memory_range().unwrap().clone()
}

/// `buffer[-1..3]` names four elements, three of them lent. Its start is
/// `4294967295` read through `as_const`, which made `start >= end` true
/// and returned the barrier's "this range names no storage" answer for a
/// range that names more storage than the lent one does.
#[test]
fn a_range_starting_below_its_base_is_not_empty_to_the_write_barrier() {
    let ledger = ledger_lending_the_first_four_elements();
    let assumptions = PureFactContext::new();
    let below = range(u32::MAX, 3);
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&below, &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    assert!(!ledger.active_memory_overlaps(&below).unwrap().is_empty());
    // The contained range is the control: a superset of a refused range
    // may never be the one that is admitted.
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&range(0, 3), &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
}

/// The exit itself stays: a backwards range is how a range says it is
/// empty, and an empty range touches no loan however far the lent range
/// reaches. Both spellings of empty, and one wholly below the loan.
#[test]
fn an_empty_or_separate_range_still_passes_the_write_barrier() {
    let ledger = ledger_lending_the_first_four_elements();
    let assumptions = PureFactContext::new();
    for empty in [range(2, 2), range(3, 1), range(u32::MAX, u32::MAX - 1)] {
        assert_eq!(
            ledger.permits_memory_access_with_assumptions(&empty, &assumptions),
            Ok(())
        );
        assert!(ledger.active_memory_overlaps(&empty).unwrap().is_empty());
    }
    // Nonempty, entirely below the lent range, and permitted on its
    // merits rather than by being mistaken for empty.
    let below = range(u32::MAX - 1, u32::MAX);
    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&below, &assumptions),
        Ok(())
    );
}

/// The same-base constant fast path in `protected_range_proven_overlapping`
/// short-circuits above the sound `byte_range` route, so reading an
/// endpoint as `u32` there is a final wrong answer. `p[-1..1]` and
/// `p[0..2]` share element `0`; zero-extension put the query's start four
/// gigabytes above the protected range's end and called them separate.
#[test]
fn a_protected_range_is_reached_from_below_its_base() {
    let assumptions = PureFactContext::new();
    let protected = range(0, 2);
    for query in [range(u32::MAX, 1), range(u32::MAX, 2), range(u32::MAX, 8)] {
        assert!(protected_range_proven_overlapping(
            &query,
            &protected,
            &assumptions
        ));
        assert!(protected_range_proven_overlapping(
            &protected,
            &query,
            &assumptions
        ));
    }
}

/// The other polarity: ranges that really are separate stay separate,
/// including two that both start below the base, and a backwards range —
/// which has no bounds to compare — is not reported as overlapping
/// everything.
#[test]
fn ranges_below_a_base_that_do_not_meet_are_still_separate() {
    let assumptions = PureFactContext::new();
    let protected = range(0, 2);
    for query in [
        range(u32::MAX - 2, u32::MAX),
        range(2, 4),
        range(u32::MAX, 0),
    ] {
        assert!(!protected_range_proven_overlapping(
            &query,
            &protected,
            &assumptions
        ));
    }
    // Two ranges wholly below the base, one inside the other.
    assert!(protected_range_proven_overlapping(
        &range(u32::MAX - 3, u32::MAX - 2),
        &range(u32::MAX - 4, u32::MAX),
        &assumptions
    ));
}

fn composite(name: &str, own: bool) -> ResourceFact {
    let resource = Resource::Composite {
        name: name.to_string(),
        arguments: Vec::new().into(),
    };
    if own {
        ResourceFact::own(resource)
    } else {
        ResourceFact::View(resource)
    }
}

#[test]
fn composite_loan_protects_primitive_frontier_and_restores_head_once() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let head = composite("cell", true);
    let piece = memory(0, 4, true);
    let context = ResourceContext::new().unchecked_with_fact(head.clone());
    let support = context.unique_owned_occurrence_for_fact(&head).unwrap().0;
    let opening = ledger
        .lend_composite(
            owner,
            reader,
            support,
            head.clone(),
            CompositeLoanBacking::from_checked_expansion(
                support,
                head.clone(),
                vec![piece.clone()],
            )
            .unwrap(),
        )
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let child = ledger
        .describe_view(
            opening.loan,
            ResourceFact::view_memory(piece.memory_range().unwrap().clone()),
            &assumptions,
        )
        .unwrap();
    assert!(ledger.permits_view(reader, &child, opening.root_share, &assumptions));
    assert_eq!(
        ledger.permits_memory_access(piece.memory_range().unwrap()),
        Err(LoanRefusal::ActiveDependency)
    );
    let end = ledger.end(opening.scope, owner);
    assert_eq!(end, Err(LoanRefusal::ShareStillSplit));
    let transfer = ledger.transfer(opening.root_share, reader, owner).unwrap();
    let ledger = ledger.apply(&transfer).unwrap();
    let end = ledger
        .apply(&ledger.end(opening.scope, owner).unwrap())
        .unwrap();
    assert!(
        end.permits_memory_access(piece.memory_range().unwrap())
            .is_ok()
    );
    let (recover, recovered, recovered_support) = end.recover(opening.loan, owner).unwrap();
    assert_eq!(recovered, head);
    assert_eq!(recovered_support, support);
    let end = end.apply(&recover).unwrap();
    assert_eq!(
        end.recover(opening.loan, owner),
        Err(LoanRefusal::AlreadyRecovered)
    );
}

#[test]
fn composite_planner_rejects_hidden_overlap_and_equal_head_ambiguity() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let head = composite("cell", true);
    let view = composite("cell", false);
    let piece = memory(0, 4, true);
    let overlapping = memory(2, 6, true);
    let context = ResourceContext::new().unchecked_with_facts([head.clone(), overlapping]);
    let support = context.unique_owned_occurrence_for_fact(&head).unwrap().0;
    let backing =
        CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![piece.clone()])
            .unwrap();
    let mut backings = BTreeMap::new();
    backings.insert(support, backing);
    let overlap = plan_stable_view_transfer_with_bindings_and_composites(
        &context,
        &[checked(view.clone())],
        &assumptions,
        &ledger,
        owner,
        reader,
        &LoanViewBindings::default(),
        &backings,
    )
    .expect_err("a hidden overlapping resource must be refused");
    assert_eq!(
        overlap
            .loan_diagnostic(LoanRefusalOperation::Plan)
            .expect("planner refusal diagnostic")
            .category(),
        LoanRefusalCategory::ProvenOverlap
    );
    let duplicate = ResourceContext::new().unchecked_with_facts([head.clone(), head]);
    let duplicate_support = duplicate
        .occurrences_for_fact(&composite("cell", true))
        .first()
        .copied()
        .unwrap();
    let mut duplicate_backings = BTreeMap::new();
    duplicate_backings.insert(
        duplicate_support,
        CompositeLoanBacking::from_checked_expansion(
            duplicate_support,
            composite("cell", true),
            vec![piece],
        )
        .unwrap(),
    );
    let duplicate_error = plan_stable_view_transfer_with_bindings_and_composites(
        &duplicate,
        &[checked(view)],
        &assumptions,
        &ledger,
        owner,
        reader,
        &LoanViewBindings::default(),
        &duplicate_backings,
    )
    .expect_err("duplicate support must be refused");
    assert_eq!(
        duplicate_error
            .loan_diagnostic(LoanRefusalOperation::Plan)
            .expect("planner refusal diagnostic")
            .category(),
        LoanRefusalCategory::Unsupported
    );
}

/// The exclusive requirements are reserved before any view is planned,
/// so the residual the composite frontier is checked against no longer
/// holds them.  A callee contract asking to own bytes its own viewed
/// composite covers must still be refused as a proven overlap, and a
/// contract whose owned clause lies outside the frontier must still plan.
#[test]
fn composite_planner_rejects_an_owned_requirement_inside_the_viewed_frontier() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let head = composite("cell", true);
    let view = composite("cell", false);
    let piece = memory(0, 4, true);
    let plan_with_owned = |owned: ResourceFact| {
        let context = ResourceContext::new().unchecked_with_facts([head.clone(), owned.clone()]);
        let support = context.unique_owned_occurrence_for_fact(&head).unwrap().0;
        let mut backings = BTreeMap::new();
        backings.insert(
            support,
            CompositeLoanBacking::from_checked_expansion(
                support,
                head.clone(),
                vec![piece.clone()],
            )
            .unwrap(),
        );
        plan_stable_view_transfer_with_bindings_and_composites(
            &context,
            &[
                CheckedResourceFact {
                    fact: owned,
                    role: ResourceTransferRole::Consume,
                    state_source: ResourceStateSource::Entry,
                    clause_position: None,
                    section_index: None,
                    selected_mutex_source: None,
                },
                checked(view.clone()),
            ],
            &assumptions,
            &ledger,
            owner,
            reader,
            &LoanViewBindings::default(),
            &backings,
        )
    };
    let overlap = plan_with_owned(memory(0, 1, true))
        .expect_err("an owned clause inside the viewed frontier must be refused");
    assert!(
        matches!(overlap, StableViewPlanError::ConflictingRequirement(_)),
        "{overlap:?}"
    );
    assert_eq!(
        overlap
            .loan_diagnostic(LoanRefusalOperation::Plan)
            .expect("planner refusal diagnostic")
            .category(),
        LoanRefusalCategory::ProvenOverlap
    );
    let disjoint = memory(4, 8, true);
    let plan = plan_with_owned(disjoint.clone())
        .expect("an owned clause outside the frontier still plans");
    assert!(
        plan.callee_resources
            .satisfies_fact(&disjoint, &assumptions)
    );
    assert_eq!(plan.stable_views().len(), 1);
}

#[test]
fn composite_planner_escrows_one_head_and_recovers_it_once() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let head = composite("cell", true);
    let view = composite("cell", false);
    let piece = memory(0, 4, true);
    let caller = ResourceContext::new().unchecked_with_fact(head.clone());
    let support = caller.unique_owned_occurrence_for_fact(&head).unwrap().0;
    let backing =
        CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![piece]).unwrap();
    let mut backings = BTreeMap::new();
    backings.insert(support, backing);
    let plan = plan_stable_view_transfer_with_bindings_and_composites(
        &caller,
        &[checked(view)],
        &assumptions,
        &ledger,
        owner,
        reader,
        &LoanViewBindings::default(),
        &backings,
    )
    .unwrap();
    assert!(
        !plan
            .caller_resources_after_requirements
            .satisfies_fact(&head, &assumptions)
    );
    assert_eq!(plan.stable_views.len(), 1);
    assert!(
        plan.ledger
            .permits_memory_access(&memory(0, 4, false).memory_range().unwrap().clone())
            .is_err()
    );
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert!(recovery.resources.satisfies_fact(&head, &assumptions));
    assert!(
        recovery
            .ledger
            .permits_memory_access(&memory(0, 4, false).memory_range().unwrap().clone())
            .is_ok()
    );
}

#[test]
fn composite_planner_keeps_other_counted_token_units_usable() {
    let (ledger, owner, reader) = participants();
    let assumptions = PureFactContext::new();
    let token = Resource::Token {
        name: "unit".into(),
        arguments: Vec::new().into(),
    };
    let owned_units = ResourceFact::own_quantity(token.clone(), MachineTerm::constant(3));
    let view = ResourceFact::View(token);
    let caller = ResourceContext::new().unchecked_with_fact(owned_units.clone());
    let plan = plan_stable_view_transfer(
        &caller,
        &[checked(view)],
        &assumptions,
        &ledger,
        owner,
        reader,
    )
    .unwrap();
    assert!(plan.caller_resources_after_requirements.satisfies_fact(
        &ResourceFact::own_quantity(
            Resource::Token {
                name: "unit".into(),
                arguments: Vec::new().into(),
            },
            MachineTerm::constant(2),
        ),
        &assumptions,
    ));
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert!(
        recovery
            .resources
            .satisfies_fact(&owned_units, &assumptions)
    );
}

#[test]
fn ordinary_view_refuses_equal_looking_replacement_after_ownership_reservation() {
    let assumptions = PureFactContext::new();
    let token = Resource::Token {
        name: "unit".into(),
        arguments: Vec::new().into(),
    };
    let owner = ResourceFact::own(token.clone());
    let caller = ResourceContext::new().unchecked_with_facts([owner.clone(), owner.clone()]);
    let mut consume = checked(owner);
    consume.role = ResourceTransferRole::Consume;
    let view = ResourceFact::View(token);
    let (ledger, caller_participant, callee_participant) = participants();

    let error = plan_stable_view_transfer(
        &caller,
        &[consume, checked(view)],
        &assumptions,
        &ledger,
        caller_participant,
        callee_participant,
    )
    .expect_err("the view must not switch to an equal-looking owner occurrence");

    assert!(
        matches!(error, StableViewPlanError::ConflictingRequirement(_)),
        "{error:?}"
    );
}

#[test]
fn memory_view_refuses_a_different_owner_after_whole_owner_reservation() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 8, true);
    let resources = ResourceContext::new().unchecked_with_facts([owner.clone(), owner.clone()]);
    let mut consume = checked(owner);
    consume.role = ResourceTransferRole::Consume;
    let (ledger, caller, callee) = participants();
    let error = plan_stable_view_transfer(
        &resources,
        &[consume, checked(memory(0, 4, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect_err("another owner cannot replace the consumed source");
    assert!(
        matches!(error, StableViewPlanError::ConflictingRequirement(_)),
        "{error:?}"
    );
}

#[test]
fn memory_split_origins_retain_both_sides_and_isolate_speculative_branches() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 12, true);
    let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let original = resources.occurrences_for_fact(&owner)[0];
    let empty_origins = MemorySplitOrigins::default();
    let (residual, _, origins) = resources
        .clone()
        .reserve_owned_memory_fragments_with_origins(
            &memory(4, 8, true),
            &assumptions,
            &empty_origins,
        )
        .unwrap();
    let support = |context: &ResourceContext, start, end| {
        context
            .directly_supporting_owned_entry(&memory(start, end, true), &assumptions)
            .unwrap()
            .0
    };
    let left = support(&residual, 0, 4);
    let right = support(&residual, 8, 12);
    assert_eq!(origins.origin_of(left), original);
    assert_eq!(origins.origin_of(right), original);
    assert_eq!(empty_origins.origin_of(left), left);

    let mut child_origins = origins.clone();
    let child = residual
        .clone()
        .without_fact_incrementally_with_origins(
            &memory(0, 2, true),
            &assumptions,
            &mut child_origins,
        )
        .unwrap();
    let child_left = support(&child, 2, 4);
    assert_eq!(child_origins.origin_of(child_left), original);
    assert_eq!(child_origins.origin_of(right), original);
    assert_eq!(origins.origin_of(child_left), child_left);
    assert_eq!(support(&residual, 0, 4), left);

    // This consumes one fragment speculatively, then encounters a gap. Its
    // discarded origin updates cannot affect the retained parent or child.
    assert!(
        child
            .clone()
            .reserve_owned_memory_fragments_with_origins(
                &memory(2, 10, true),
                &assumptions,
                &child_origins,
            )
            .is_none()
    );
    assert!(
        child
            .clone()
            .without_fact_incrementally_with_origins(
                &memory(2, 10, true),
                &assumptions,
                &mut child_origins,
            )
            .is_none()
    );
    assert_eq!(child_origins.origin_of(child_left), original);
    assert_eq!(child_origins.origin_of(right), original);
}

/// Step 7: a loan a produced borrowing composite escapes through is not
/// recovered at return; the caller keeps the escrow lent, holds the
/// loan through the composite's binding, and recovers the owner only
/// when a later call consumes the composite.
#[test]
fn escaping_borrow_keeps_the_loan_open_until_the_composite_is_consumed() {
    let assumptions = PureFactContext::new();
    let owner_fact = memory(0, 8, true);
    let viewed = memory(0, 8, false);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner_fact.clone());
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(viewed.clone())],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect("the view is lent from the owner");
    let loan = plan.stable_views()[0].loan;
    let head = composite("cursor", true);
    let mut escaping = BTreeMap::new();
    escaping.insert(loan, vec![head.clone()]);
    let planned_ledger = plan.ledger.clone();
    let recovery = plan
        .clone()
        .recover_stable_views(&assumptions, &escaping, &[])
        .expect("an escaping loan recovers open");
    let evidence = CheckedLoanCallEvidence::new(
        plan.clone(),
        recovery.ledger.clone(),
        recovery.terminal_ledger.clone(),
        recovery.transitions.clone(),
        recovery.hold_base_ledger.clone(),
        recovery.hold_transitions.clone(),
    );
    assert!(
        evidence
            .recheck(&ledger, Some(caller), &planned_ledger, Some(callee))
            .is_ok()
    );
    assert!(
        recovery.recovered_escrows.is_empty(),
        "the owner stays escrowed"
    );
    assert!(!recovery.resources.satisfies_fact(&owner_fact, &assumptions));
    assert_eq!(recovery.escaped_holds.len(), 1);
    let escaped = &recovery.escaped_holds[0];
    assert_eq!(escaped.head, head);
    let hold = escaped.binding.hold.expect("the composite carries a hold");
    let open = recovery.ledger;
    assert!(open.invariant_holds());
    assert!(
        open.has_active_memory_loans(),
        "the lent bytes stay protected"
    );
    assert_eq!(
        open.permits_memory_access_with_assumptions(
            &memory(0, 8, true).memory_own_range().unwrap().clone(),
            &assumptions
        ),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(open.held_scope(hold), Some(escaped.binding.scope));
    assert_eq!(
        open.end(escaped.binding.scope, caller),
        Err(LoanRefusal::ActiveDependency),
        "the held scope cannot be ended behind the composite's back"
    );
    assert_ne!(
        recovery.terminal_ledger, open,
        "adding an escaped hold changes the ledger identity"
    );
    assert_eq!(
        recovery.terminal_ledger, recovery.hold_base_ledger,
        "the escaped hold is rechecked from the checked terminal ledger"
    );

    // A later call consumes the composite: its hold is released, the
    // root ends, and the owner comes back.
    let next = plan_stable_view_transfer(
        &recovery.resources,
        &[],
        &assumptions,
        &open,
        caller,
        open.fresh_participant().unwrap(),
    )
    .expect("an empty plan on the open ledger");
    let next_callee_ledger = next.ledger.clone();
    let next_callee_participant = next.callee_participant();
    let recovered = next
        .clone()
        .recover_stable_views(
            &assumptions,
            &BTreeMap::new(),
            std::slice::from_ref(&escaped.binding),
        )
        .expect("consuming the composite recovers the owner");
    let recovered_ledger = recovered.ledger.clone();
    let next_evidence = Arc::new(CheckedLoanCallEvidence::new(
        next,
        recovered.ledger.clone(),
        recovered.terminal_ledger.clone(),
        recovered.transitions.clone(),
        recovered.hold_base_ledger.clone(),
        recovered.hold_transitions.clone(),
    ));
    assert!(
        next_evidence
            .recheck(
                &open,
                Some(caller),
                &next_callee_ledger,
                Some(next_callee_participant)
            )
            .is_ok()
    );
    let sequence = append_checked_loan_evidence(
        &empty_checked_loan_evidence_sequence(),
        Some(Arc::new(evidence)),
    );
    let sequence = append_checked_loan_evidence(&sequence, Some(next_evidence));
    assert_eq!(
        sequence.recovered_ledger_for(&ledger, caller, false),
        Some(recovered_ledger.clone()),
        "the path summary follows state-changing holds to the final recovery"
    );
    assert_eq!(
        sequence.pristine_recovery(),
        (Some(caller), Some(recovered_ledger.clone())),
        "pristine-root summaries follow the same recovery chain"
    );
    assert_eq!(
        recovered.recovered_escrows,
        vec![(owner_fact.clone(), None)]
    );
    assert!(
        recovered
            .resources
            .satisfies_fact(&owner_fact, &assumptions)
    );
    assert!(recovered.ledger.invariant_holds());
    assert!(!recovered.ledger.has_active_memory_loans());
    assert_eq!(recovered.ledger.held_scope(hold), None);
    assert!(
        recovered
            .ledger
            .permits_memory_access_with_assumptions(
                &owner_fact.memory_own_range().unwrap().clone(),
                &assumptions
            )
            .is_ok()
    );
}

#[test]
fn composite_backing_tamper_and_instance_frontier_are_refused() {
    let (ledger, owner, reader) = participants();
    let head = composite("cell", true);
    let support = backing(&head);
    // A nested composite child is admitted as a permitted description,
    // and so is a viewed piece: a borrowing composite packages a
    // description its hold keeps stable (step 7). Neither carries byte
    // backing of its own.
    let nested = composite("nested", true);
    assert!(
        CompositeLoanBacking::from_checked_expansion(support, head.clone(), vec![nested]).is_some()
    );
    assert!(
        CompositeLoanBacking::from_checked_expansion(
            support,
            head.clone(),
            vec![composite("nested", false)]
        )
        .is_some()
    );
    // A backing whose head is not the escrow is not this composite's
    // checked expansion, whatever it was built from.
    let tampered = CompositeLoanBacking {
        support,
        head: composite("other", true),
        pieces: Vec::new(),
        adapted: Vec::new(),
        restored: Vec::new(),
    };
    let unsupported = ledger
        .lend_composite(owner, reader, support, head, tampered)
        .expect_err("tampered composite backing must be refused");
    assert_eq!(
        unsupported
            .diagnostic(LoanRefusalOperation::Transition)
            .category(),
        LoanRefusalCategory::Unsupported
    );
    let mut opening = ledger
        .lend_composite(
            owner,
            reader,
            support,
            composite("cell", true),
            CompositeLoanBacking::from_checked_expansion(
                support,
                composite("cell", true),
                Vec::new(),
            )
            .unwrap(),
        )
        .unwrap();
    let LoanTransitionEvidence::LendComposite { support_fact, .. } =
        &mut opening.transition.evidence
    else {
        panic!("composite lend evidence")
    };
    *support_fact = ResourceFact::own_token("other".into(), Vec::new());
    let invalid = ledger
        .apply(&opening.transition)
        .expect_err("tampered occurrence evidence must be refused");
    assert_eq!(
        invalid
            .diagnostic(LoanRefusalOperation::Transition)
            .category(),
        LoanRefusalCategory::InvalidEvidence
    );
}

fn symbolic_memory(start: MachineTerm, end: MachineTerm, own: bool) -> ResourceFact {
    let range = crate::kernel::MemoryRange::new(
        crate::kernel::Pointer {
            block: "buffer".into(),
            offset: crate::kernel::PointerOffsetTerm::Constant(0),
        },
        start,
        end,
    );
    if own {
        ResourceFact::own_memory(range)
    } else {
        ResourceFact::view_memory(range)
    }
}

#[test]
fn joint_planner_uses_one_escrow_for_overlapping_views_and_recovers_it() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 9, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[
            checked(memory(0, 6, false)),
            checked(memory(2, 8, false)),
            checked(memory(7, 9, false)),
        ],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    assert_eq!(plan.stable_views.len(), 3);
    assert_eq!(plan.stable_views[0].loan, plan.stable_views[1].loan);
    assert_eq!(plan.stable_views[0].share, plan.stable_views[1].share);
    assert!(
        !plan
            .caller_resources_after_requirements
            .satisfies_fact(&owner, &assumptions)
    );
    for planned in &plan.stable_views {
        assert!(plan.ledger.permits_view(
            callee,
            &planned.description,
            planned.share,
            &assumptions
        ));
    }
    let planned_ledger = plan.ledger.clone();
    let rechecked = plan.recheck_entry(&ledger).unwrap();
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert!(recovery.resources.satisfies_fact(&owner, &assumptions));
    assert_eq!(recovery.transitions.len(), 3);
    assert_eq!(recovery.ledger, ledger);
    assert_eq!(rechecked, planned_ledger);
    assert!(
        recovery
            .recheck_transitions(&planned_ledger, caller)
            .is_ok()
    );
}

#[test]
fn joint_planner_returns_disjoint_residual_ranges_and_exact_backing() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 8, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(2, 4, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let planned = &plan.stable_views[0];
    let (support, _) = caller_resources
        .directly_supporting_owned_entry(&owner, &assumptions)
        .unwrap();
    assert_eq!(planned.support, support);
    assert_eq!(planned.description.support(), support);
    assert!(
        plan.caller_resources_after_requirements
            .satisfies_fact(&memory(0, 2, true), &assumptions)
    );
    assert!(
        plan.caller_resources_after_requirements
            .satisfies_fact(&memory(4, 8, true), &assumptions)
    );
    assert!(
        !plan
            .caller_resources_after_requirements
            .satisfies_fact(&owner, &assumptions)
    );
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert!(recovery.resources.satisfies_fact(&owner, &assumptions));
    assert_eq!(recovery.ledger, ledger);
}

#[test]
fn joint_planner_reserves_owned_fragments_once_and_retains_each_support() {
    let facts = PureFactContext::new();
    let pieces = [memory(0, 2, true), memory(2, 3, true), memory(3, 4, true)];
    let resources = pieces
        .iter()
        .fold(ResourceContext::new(), |resources, piece| {
            resources.unchecked_with_fact(piece.clone())
        });
    resources.synchronize_memory_equalities(&facts);
    let (ledger, caller, callee) = participants();
    let required = checked(memory(0, 4, true));
    let plan = plan_stable_view_transfer(
        &resources,
        std::slice::from_ref(&required),
        &facts,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    assert!(plan.callee_resources.satisfies_fact(&required.fact, &facts));
    assert!(plan.caller_resources_after_requirements.facts().is_empty());
    assert_eq!(plan.reserved_ownership_supports.len(), 3);
    for (fact, support) in &plan.reserved_ownership_supports {
        assert_eq!(fact, &required.fact);
        assert!(resources.owned_fact_for_occurrence(*support).is_some());
    }
    assert!(
        plan_stable_view_transfer(
            &resources,
            &[required.clone(), required.clone()],
            &facts,
            &ledger,
            caller,
            callee
        )
        .is_err()
    );
    assert!(
        plan_stable_view_transfer(
            &plan.caller_resources_after_requirements,
            &[required],
            &facts,
            &ledger,
            caller,
            callee
        )
        .is_err()
    );
}

#[test]
fn joint_planner_rechecks_two_disjoint_entry_loans_by_exact_state_chain() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 8, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(0, 2, false)), checked(memory(6, 8, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    assert_eq!(plan.entry_transitions.len(), 2);
    assert_ne!(plan.stable_views[0].support, plan.stable_views[1].support);
    let planned_ledger = plan.ledger.clone();
    assert_eq!(plan.recheck_entry(&ledger).unwrap(), planned_ledger);
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert_eq!(recovery.ledger, ledger);
    assert_eq!(recovery.transitions.len(), 6);
    assert!(
        recovery
            .recheck_transitions(&planned_ledger, caller)
            .is_ok()
    );
}

#[test]
fn joint_planner_empty_views_need_no_backing_or_loan() {
    let assumptions = PureFactContext::new();
    let resources = ResourceContext::new();
    let (ledger, caller, callee) = participants();
    let endpoint = MachineTerm::Variable(Variable(71_003));
    for view in [
        memory(0, 0, false),
        symbolic_memory(endpoint.clone(), endpoint, false),
    ] {
        let plan = plan_stable_view_transfer(
            &resources,
            &[checked(view.clone())],
            &assumptions,
            &ledger,
            caller,
            callee,
        )
        .unwrap();
        assert!(plan.stable_views.is_empty());
        assert!(plan.entry_transitions.is_empty());
        assert!(plan.callee_resources.satisfies_fact(&view, &assumptions));
        assert_eq!(plan.recheck_entry(&ledger).unwrap(), ledger);
        let recovery = plan
            .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
            .unwrap();
        assert_eq!(recovery.ledger, ledger);
    }
    let nonempty = memory(0, 1, false);
    assert_eq!(
        plan_stable_view_transfer(
            &resources,
            &[checked(nonempty.clone())],
            &assumptions,
            &ledger,
            caller,
            callee,
        ),
        Err(StableViewPlanError::MissingResource(nonempty))
    );
}

#[test]
fn joint_planner_refuses_an_uncovered_symbolic_view_without_consuming_state() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 8, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (ledger, caller, callee) = participants();
    let before = ledger.clone();
    let symbolic = symbolic_memory(
        MachineTerm::Variable(Variable(71_001)),
        MachineTerm::constant(4),
        false,
    );
    // Nothing bounds the symbolic start, so the concrete owner does not
    // entail the requested range and there is no backing to select.
    assert_eq!(
        plan_stable_view_transfer(
            &caller_resources,
            &[checked(symbolic.clone())],
            &assumptions,
            &ledger,
            caller,
            callee,
        ),
        Err(StableViewPlanError::MissingResource(symbolic))
    );
    assert!(ledger.shares_storage_with(&before));
}

#[test]
fn joint_planner_backs_a_covered_symbolic_view_with_its_whole_owner() {
    let assumptions = PureFactContext::new();
    let end = MachineTerm::Variable(Variable(71_002));
    let owner = symbolic_memory(MachineTerm::constant(0), end.clone(), true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (ledger, caller, callee) = participants();
    let view = symbolic_memory(MachineTerm::constant(0), end, false);
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(view.clone())],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect("a covering owner backs a symbolic view range");
    assert_eq!(plan.stable_views.len(), 1);
    assert_eq!(plan.stable_views[0].requirement.fact, view);
    // The whole covering owner is escrowed: the algebra cannot split a
    // symbolic range, so no writable remainder may be left behind.
    assert!(
        plan.caller_resources_after_requirements
            .facts()
            .iter()
            .all(|fact| *fact != owner)
    );
    assert!(plan.callee_resources.satisfies_fact(&view, &assumptions));
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert_eq!(recovery.ledger, ledger);
    assert!(recovery.resources.satisfies_fact(&owner, &assumptions));
}

#[test]
fn joint_planner_shares_one_loan_between_two_covered_symbolic_views() {
    let assumptions = PureFactContext::new();
    let end = MachineTerm::Variable(Variable(71_003));
    let owner = symbolic_memory(MachineTerm::constant(0), end.clone(), true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
    let (ledger, caller, callee) = participants();
    let first = symbolic_memory(MachineTerm::constant(0), end.clone(), false);
    let second = symbolic_memory(MachineTerm::constant(0), end, false);
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(first), checked(second)],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect("two covered symbolic views share the covering owner");
    // Law 8: unknown aliasing between the two requested ranges may not be
    // resolved into two escrows of the same bytes.
    assert_eq!(plan.entry_transitions.len(), 1);
    assert_eq!(plan.stable_views.len(), 2);
    assert_eq!(plan.stable_views[0].loan, plan.stable_views[1].loan);
}

/// Every view the plan composes into the callee context carries its loan
/// binding on the occurrence itself, not only in the plan's sidecar. The
/// sidecar alone left the fact indistinguishable from an unbound view, so
/// normalization was free to merge it with a neighbour and the
/// per-requirement occurrence lookup then failed with `InvalidResidual`.
#[test]
fn joint_planner_binds_every_composed_callee_view_occurrence() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 5, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner);
    let (ledger, caller, callee) = participants();
    let first = memory(0, 1, false);
    let second = memory(3, 4, false);
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(first.clone()), checked(second.clone())],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect("two views plan from one owner");
    assert_eq!(plan.stable_views.len(), 2);
    let bound = plan
        .callee_resources
        .live_loan_dependencies()
        .map(|(occurrence, binding)| (occurrence, binding.viewed.clone()))
        .collect::<Vec<_>>();
    assert_eq!(bound.len(), 2);
    assert_ne!(bound[0].0, bound[1].0);
    assert!(bound.iter().any(|(_, viewed)| *viewed == first));
    assert!(bound.iter().any(|(_, viewed)| *viewed == second));
}

#[test]
fn joint_planner_refuses_an_unbound_view_the_caller_does_not_own() {
    let assumptions = PureFactContext::new();
    let caller_resources = ResourceContext::new().unchecked_with_fact(memory(0, 8, false));
    let (ledger, caller, callee) = participants();
    // A view description with no loan binding is not authority, and no
    // owner covers the requirement either.
    assert_eq!(
        plan_stable_view_transfer(
            &caller_resources,
            &[checked(memory(0, 4, false))],
            &assumptions,
            &ledger,
            caller,
            callee,
        ),
        Err(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))
    );
}

#[test]
fn joint_planner_lends_from_the_owner_beside_an_unbound_view_description() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 8, true);
    let caller_resources = ResourceContext::new()
        .unchecked_with_fact(owner)
        .unchecked_with_fact(memory(0, 8, false));
    let (ledger, caller, callee) = participants();
    let plan = plan_stable_view_transfer(
        &caller_resources,
        &[checked(memory(0, 4, false))],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect("the owner backs the view that the stale description cannot");
    assert_eq!(plan.stable_views.len(), 1);
    assert_eq!(plan.entry_transitions.len(), 1);
}

#[test]
fn active_child_dependency_blocks_parent_close_until_child_ends() {
    let (ledger, owner, reader) = participants();
    let parent = lend_test(&ledger, owner, owner, owned("parent"));
    let ledger = ledger.apply(&parent.transition).unwrap();
    let child = lend_test(&ledger, owner, reader, owned("child"));
    let ledger = ledger.apply(&child.transition).unwrap();
    let dependency = ledger
        .register_dependency(parent.scope, child.scope, owner)
        .unwrap();
    let ledger = ledger.apply(&dependency).unwrap();
    assert_eq!(
        ledger.end(parent.scope, owner),
        Err(LoanRefusal::ActiveDependency)
    );
    let child_return = ledger.transfer(child.root_share, reader, owner).unwrap();
    let ledger = ledger.apply(&child_return).unwrap();
    let child_end = ledger.end(child.scope, owner).unwrap();
    let ledger = ledger.apply(&child_end).unwrap();
    assert!(ledger.end(parent.scope, owner).is_ok());
}

#[test]
fn joint_planner_rejects_view_and_mutable_transfer_of_same_authority() {
    let assumptions = PureFactContext::new();
    let owner = memory(0, 8, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    let (ledger, caller, callee) = participants();
    let requirements = [
        checked(memory(0, 4, false)),
        CheckedResourceFact {
            fact: owner,
            role: ResourceTransferRole::Consume,
            state_source: ResourceStateSource::Entry,
            clause_position: None,
            section_index: None,
            selected_mutex_source: None,
        },
    ];
    assert!(matches!(
        plan_stable_view_transfer(
            &caller_resources,
            &requirements,
            &assumptions,
            &ledger,
            caller,
            callee,
        ),
        Err(StableViewPlanError::ConflictingRequirement(_))
    ));
}

#[test]
fn joint_planner_partitions_disjoint_write_and_view_ranges_in_any_clause_order() {
    let assumptions = PureFactContext::new();
    let caller_resources = ResourceContext::new().unchecked_with_fact(memory(0, 8, true));
    let (ledger, caller, callee) = participants();
    let write = CheckedResourceFact {
        fact: memory(4, 8, true),
        role: ResourceTransferRole::Consume,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    };
    let read = checked(memory(0, 4, false));
    let left = plan_stable_view_transfer(
        &caller_resources,
        &[write.clone(), read.clone()],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    let right = plan_stable_view_transfer(
        &caller_resources,
        &[read.clone(), write.clone()],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .unwrap();
    for plan in [&left, &right] {
        assert!(
            plan.callee_resources
                .satisfies_fact(&write.fact, &assumptions)
        );
        assert!(
            plan.callee_resources
                .satisfies_fact(&read.fact, &assumptions)
        );
        assert_eq!(
            plan.memory_effects,
            vec![write.fact.memory_own_range().unwrap().clone()]
        );
        assert_eq!(plan.stable_views.len(), 1);
    }
    // Whole-context equality is not the right comparison here: each plan
    // binds its composed view occurrences, and an occurrence identity is
    // freshly allocated per plan by construction (law 5). Compare what
    // clause order must not change: the facts, and the viewed fact each
    // live binding carries.
    assert_eq!(
        left.callee_resources.facts(),
        right.callee_resources.facts()
    );
    let bound = |plan: &StableViewTransferPlan| {
        plan.callee_resources
            .live_loan_dependencies()
            .map(|(_, binding)| binding.viewed.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(bound(&left), vec![read.fact.clone()]);
    assert_eq!(bound(&left), bound(&right));
    assert_eq!(left.memory_effects, right.memory_effects);

    let reverse_write = CheckedResourceFact {
        fact: memory(0, 4, true),
        role: ResourceTransferRole::Consume,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    };
    let reverse_view = checked(memory(6, 8, false));
    let reverse = plan_stable_view_transfer(
        &caller_resources,
        &[reverse_write.clone(), reverse_view.clone()],
        &assumptions,
        &ledger,
        caller,
        callee,
    )
    .expect("a residual fragment of the unique owner retains its provenance");
    assert!(
        reverse
            .callee_resources
            .satisfies_fact(&reverse_write.fact, &assumptions)
    );
    assert!(
        reverse
            .callee_resources
            .satisfies_fact(&reverse_view.fact, &assumptions)
    );
}

#[test]
fn rejected_joint_plan_leaves_caller_resources_and_ledger_unchanged() {
    let assumptions = PureFactContext::new();
    let owned = memory(0, 4, true);
    let caller_resources = ResourceContext::new().unchecked_with_fact(owned.clone());
    let resources_before = caller_resources.clone();
    let (ledger, caller, callee) = participants();
    let ledger_before = ledger.clone();
    let missing = ResourceFact::own_token("missing".to_string(), Vec::new());
    let requirements = [
        checked(memory(0, 4, false)),
        CheckedResourceFact {
            fact: missing.clone(),
            role: ResourceTransferRole::Consume,
            state_source: ResourceStateSource::Entry,
            clause_position: None,
            section_index: None,
            selected_mutex_source: None,
        },
    ];
    assert_eq!(
        plan_stable_view_transfer(
            &caller_resources,
            &requirements,
            &assumptions,
            &ledger,
            caller,
            callee,
        ),
        Err(StableViewPlanError::MissingResource(missing))
    );
    assert_eq!(caller_resources, resources_before);
    assert!(ledger.shares_storage_with(&ledger_before));
    assert!(caller_resources.satisfies_fact(&owned, &assumptions));
}

#[test]
fn joint_planner_refuses_an_independent_view_without_owned_support() {
    let assumptions = PureFactContext::new();
    let view = memory(0, 4, false);
    let caller_resources = ResourceContext::new().unchecked_with_fact(view.clone());
    let (ledger, caller, callee) = participants();
    assert_eq!(
        plan_stable_view_transfer(
            &caller_resources,
            &[checked(view.clone())],
            &assumptions,
            &ledger,
            caller,
            callee,
        ),
        Err(StableViewPlanError::Loan(LoanRefusal::MissingLoanBinding))
    );
}

#[test]
fn nested_view_reborrow_pins_parent_and_restores_exact_binding() {
    let assumptions = PureFactContext::new();
    let owned_range = memory(0, 8, true);
    let support = backing(&owned_range);
    let parent_view = memory(0, 8, false);
    let child_views = [memory(2, 4, false), memory(6, 8, false)];
    let (ledger, owner, reader) = participants();
    let opening = ledger
        .lend(owner, owner, support, owned_range.clone())
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let parent_binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support,
        viewed: parent_view.clone(),
        hold: None,
    };
    let parent_resources = ResourceContext::new().unchecked_with_fact(parent_view.clone());
    let (occurrence, _) = parent_resources
        .view_occurrences_for_fact(&parent_view, &assumptions)
        .into_iter()
        .map(|occurrence| (occurrence, ()))
        .next()
        .expect("parent view occurrence");
    let parent_bindings = LoanViewBindings::default().with_inserted(occurrence, parent_binding);
    let plan = plan_stable_view_transfer_with_bindings(
        &parent_resources,
        &child_views.iter().cloned().map(checked).collect::<Vec<_>>(),
        &assumptions,
        &ledger,
        owner,
        reader,
        &parent_bindings,
    )
    .unwrap();
    assert_eq!(plan.stable_views.len(), child_views.len());
    for (child, viewed) in plan.stable_views.iter().zip(&child_views) {
        assert_ne!(child.loan, opening.loan);
        assert_eq!(child.description.viewed(), viewed);
        assert!(
            plan.ledger
                .permits_view(reader, &child.description, child.share, &assumptions)
        );
    }
    assert!(!plan.ledger.permits_view(
        owner,
        &opening.description,
        opening.root_share,
        &assumptions
    ));
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert_eq!(recovery.ledger, ledger);
    assert_eq!(recovery.view_bindings, parent_bindings);
    assert!(
        recovery
            .resources
            .satisfies_fact(&parent_view, &assumptions)
    );
}

#[test]
fn nested_view_reborrow_accepts_checked_offset_alias_and_preserves_authority() {
    let base = crate::kernel::Pointer::symbolic(Variable(72_000));
    let alias = crate::kernel::Pointer::symbolic(Variable(72_001));
    let offset = MachineTerm::Variable(Variable(72_002));
    let empty = PureFactContext::new();
    let assumptions = empty
        .clone()
        .assume_condition(
            crate::kernel::ConditionTerm::pointer_equal(
                alias.clone(),
                base.offset_by_elements(offset.clone(), 1),
            ),
            true,
        )
        .assume_condition(
            crate::kernel::ConditionTerm::signed_less_equal(0u32.into(), offset.clone()),
            true,
        )
        .assume_condition(
            crate::kernel::ConditionTerm::signed_less_equal(
                MachineTerm::add(offset, 4u32.into()),
                16u32.into(),
            ),
            true,
        );
    let range = |pointer, end| {
        crate::kernel::MemoryRange::new_with_element_width(pointer, 0u32.into(), end, 1)
    };
    let owned = ResourceFact::own_memory(range(base.clone(), 16u32.into()));
    let parent_view = ResourceFact::view_memory(range(base, 16u32.into()));
    let child_view = ResourceFact::view_memory(range(alias.clone(), 4u32.into()));
    let (ledger, caller, callee) = participants();
    let opening = lend_test(&ledger, caller, caller, owned);
    let ledger = ledger.apply(&opening.transition).unwrap();
    let resources =
        ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(parent_view.clone());
    let occurrence = resources.occurrences_for_fact(&parent_view)[0];
    let bindings = LoanViewBindings::default().with_inserted(
        occurrence,
        LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: opening.description.support(),
            viewed: parent_view.clone(),
            hold: None,
        },
    );
    let plan = plan_stable_view_transfer_with_bindings(
        &resources,
        &[checked(child_view.clone())],
        &assumptions,
        &ledger,
        caller,
        callee,
        &bindings,
    )
    .expect("checked offset alias selects the bound parent view");
    assert!(
        plan.callee_resources
            .satisfies_fact(&child_view, &assumptions)
    );
    let recovery = plan
        .recover_stable_views(&assumptions, &BTreeMap::new(), &[])
        .unwrap();
    assert_eq!(recovery.ledger, ledger);
    assert_eq!(recovery.view_bindings, bindings);
    for (facts, view, bound) in [
        (&empty, child_view.clone(), &bindings),
        (
            &assumptions,
            ResourceFact::view_memory(range(alias, 17u32.into())),
            &bindings,
        ),
        (&assumptions, child_view, &LoanViewBindings::default()),
    ] {
        assert!(
            plan_stable_view_transfer_with_bindings(
                &resources,
                &[checked(view)],
                facts,
                &ledger,
                caller,
                callee,
                bound,
            )
            .is_err()
        );
    }
}

#[test]
fn nested_view_reborrow_rejects_wider_child_than_bound_parent() {
    let assumptions = PureFactContext::new();
    let owned_range = memory(0, 8, true);
    let parent_view = memory(2, 4, false);
    let wider_view = memory(0, 8, false);
    let (ledger, owner, reader) = participants();
    let opening = lend_test(&ledger, owner, owner, owned_range);
    let ledger = ledger.apply(&opening.transition).unwrap();
    let parent_resources = ResourceContext::new().unchecked_with_fact(wider_view.clone());
    let occurrence = parent_resources
        .view_occurrences_for_fact(&wider_view, &assumptions)
        .into_iter()
        .next()
        .expect("wider view occurrence");
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: opening.description.support(),
        viewed: parent_view,
        hold: None,
    };
    let bindings = LoanViewBindings::default().with_inserted(occurrence, binding);
    let invalid = plan_stable_view_transfer_with_bindings(
        &parent_resources,
        &[checked(wider_view)],
        &assumptions,
        &ledger,
        owner,
        reader,
        &bindings,
    )
    .expect_err("a wider range than the bound view must be refused");
    assert_eq!(
        invalid
            .loan_diagnostic(LoanRefusalOperation::Plan)
            .expect("planner refusal diagnostic")
            .category(),
        LoanRefusalCategory::InvalidEvidence
    );
}

#[test]
fn active_memory_index_returns_only_overlapping_live_loans() {
    let owned_range = memory(0, 8, true);
    let (ledger, owner, reader) = participants();
    let opening = ledger
        .lend(owner, reader, backing(&owned_range), owned_range)
        .unwrap();
    let ledger = ledger.apply(&opening.transition).unwrap();
    let protected_state = ledger.clone();
    assert!(ledger.has_active_memory_loans());
    assert!(ledger.has_indexed_memory_overlap(memory(2, 4, false).memory_range().unwrap()));
    assert!(!ledger.has_indexed_memory_overlap(memory(8, 10, false).memory_range().unwrap()));
    assert!(!ledger.has_indexed_memory_overlap(memory(8, 8, false).memory_range().unwrap()));
    assert!(!ledger.has_indexed_memory_overlap(&parameter_range(41, 0, 1, 4)));
    assert_eq!(
        ledger
            .active_memory_overlaps(memory(2, 4, false).memory_range().unwrap())
            .unwrap(),
        vec![opening.loan]
    );
    assert!(
        ledger
            .active_memory_overlaps(memory(8, 10, false).memory_range().unwrap())
            .unwrap()
            .is_empty()
    );
    assert!(
        ledger
            .permits_memory_access(memory(8, 10, false).memory_range().unwrap())
            .is_ok()
    );
    assert!(
        ledger
            .permits_memory_access(memory(8, 8, false).memory_range().unwrap())
            .is_ok()
    );
    let blocked = ledger
        .permits_memory_access(memory(2, 4, false).memory_range().unwrap())
        .expect_err("a live loan must block overlapping memory access");
    assert_eq!(
        blocked
            .diagnostic(LoanRefusalOperation::MemoryAccess)
            .category(),
        LoanRefusalCategory::ActiveDependency
    );
    let returned = ledger.transfer(opening.root_share, reader, owner).unwrap();
    let ledger = ledger.apply(&returned).unwrap();
    let ended = ledger.end(opening.scope, owner).unwrap();
    let ledger = ledger.apply(&ended).unwrap();
    assert!(
        ledger
            .active_memory_overlaps(memory(2, 4, false).memory_range().unwrap())
            .unwrap()
            .is_empty()
    );
    assert!(
        ledger
            .permits_memory_access(memory(2, 4, false).memory_range().unwrap())
            .is_ok()
    );
    assert!(!ledger.has_indexed_memory_overlap(memory(2, 4, false).memory_range().unwrap()));
    assert!(
        protected_state.has_indexed_memory_overlap(memory(2, 4, false).memory_range().unwrap())
    );
    assert!(!ledger.has_active_memory_loans());
    assert!(protected_state.has_active_memory_loans());
    assert_eq!(
        protected_state.permits_memory_access(memory(2, 4, false).memory_range().unwrap()),
        Err(LoanRefusal::ActiveDependency)
    );
    let _ = ledger.recover(opening.loan, owner).unwrap();
}

#[test]
fn indexed_loan_blocks_write_through_exact_pointer_alias() {
    let (ledger, owner, reader) = participants();
    let protected_base = Pointer {
        block: PointerBlock::Symbolic(Variable(702)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let protected = ResourceFact::own_memory(MemoryRange::new(
        protected_base.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    ));
    let opening = lend_test(&ledger, owner, reader, protected);
    let ledger = ledger.apply(&opening.transition).unwrap();

    let query_base = Pointer {
        block: PointerBlock::Symbolic(Variable(703)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(query_base.clone(), protected_base.clone()),
        true,
    );
    assert!(
        assumptions
            .exact_pointer_aliases(&query_base)
            .any(|alias| alias == &protected_base)
    );
    let query = MemoryRange::new(
        query_base,
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );

    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&query, &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
    assert_eq!(
        ledger
            .memory_access_refusal(&query, &assumptions, LoanRefusalOperation::MemoryAccess,)
            .unwrap()
            .category(),
        LoanRefusalCategory::ActiveDependency
    );
}

#[test]
fn symbolic_loan_fallback_checks_equal_pointer_alias_buckets() {
    let (ledger, owner, reader) = participants();
    let protected_base = Pointer {
        block: PointerBlock::Symbolic(Variable(704)),
        offset: PointerOffsetTerm::Variable(Variable(700)),
    };
    let protected = MemoryRange::new_with_element_width(
        protected_base.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
        4,
    );
    let opening = lend_test(&ledger, owner, reader, ResourceFact::own_memory(protected));
    let ledger = ledger.apply(&opening.transition).unwrap();

    let query_base = Pointer {
        block: PointerBlock::Symbolic(Variable(705)),
        offset: PointerOffsetTerm::Variable(Variable(701)),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(query_base.clone(), protected_base.clone()),
        true,
    );
    assert!(
        assumptions
            .exact_pointer_aliases(&query_base)
            .any(|alias| alias == &protected_base)
    );
    let query = MemoryRange::new_with_element_width(
        query_base,
        MachineTerm::constant(0),
        MachineTerm::constant(1),
        4,
    );

    assert_eq!(
        ledger.permits_memory_access_with_assumptions(&query, &assumptions),
        Err(LoanRefusal::ActiveDependency)
    );
}

#[test]
fn ending_nested_memory_loan_keeps_parent_footprint_indexed() {
    let owned_range = memory(0, 8, true);
    let (ledger, owner, reader) = participants();
    let parent = ledger
        .lend(owner, owner, backing(&owned_range), owned_range.clone())
        .unwrap();
    let ledger = ledger.apply(&parent.transition).unwrap();
    let parent_binding = LoanViewBinding {
        loan: parent.loan,
        scope: parent.scope,
        share: parent.root_share,
        support: parent.description.support(),
        viewed: memory(0, 8, false),
        hold: None,
    };
    let child = ledger.reborrow(parent_binding, owner, reader).unwrap();
    let ledger = ledger.apply(&child.transition).unwrap();
    let overlapping_fact = memory(1, 2, false);
    let overlapping = overlapping_fact.memory_range().unwrap();
    let active = ledger.active_memory_overlaps(overlapping).unwrap();
    assert!(active.contains(&parent.loan));
    assert!(active.contains(&child.loan));

    let child_return = ledger.transfer(child.root_share, reader, owner).unwrap();
    let ledger = ledger.apply(&child_return).unwrap();
    let child_end = ledger.end(child.scope, owner).unwrap();
    let ledger = ledger.apply(&child_end).unwrap();
    assert_eq!(
        ledger.active_memory_overlaps(overlapping).unwrap(),
        vec![parent.loan]
    );
    let blocked = ledger
        .permits_memory_access(overlapping)
        .expect_err("the parent loan must remain indexed");
    assert_eq!(
        blocked
            .diagnostic(LoanRefusalOperation::MemoryAccess)
            .category(),
        LoanRefusalCategory::ActiveDependency
    );

    let parent_end = ledger.end(parent.scope, owner).unwrap();
    let ledger = ledger.apply(&parent_end).unwrap();
    assert!(
        ledger
            .active_memory_overlaps(overlapping)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn refusal_diagnostics_preserve_overlap_and_boundary_categories() {
    let active = LoanRefusal::ActiveDependency.diagnostic(LoanRefusalOperation::MemoryAccess);
    assert_eq!(active.category(), LoanRefusalCategory::ActiveDependency);
    assert_eq!(active.overlap(), LoanOverlapStatus::ProvenOverlap);

    let unsupported = LoanRefusal::UnsupportedPartition.diagnostic(LoanRefusalOperation::Plan);
    assert_eq!(
        unsupported.category(),
        LoanRefusalCategory::SeparationUnproved
    );
    assert_eq!(unsupported.overlap(), LoanOverlapStatus::SeparationUnproved);

    let wrong_holder = LoanRefusal::WrongHolder.diagnostic(LoanRefusalOperation::Recovery);
    assert_eq!(wrong_holder.category(), LoanRefusalCategory::WrongHolder);
    let wrong_scope = LoanRefusal::WrongScope.diagnostic(LoanRefusalOperation::Transition);
    assert_eq!(wrong_scope.category(), LoanRefusalCategory::WrongScope);
    let stale = LoanRefusal::StalePredecessor.diagnostic(LoanRefusalOperation::Recovery);
    assert_eq!(stale.category(), LoanRefusalCategory::StalePredecessor);
    let recovery = LoanRefusal::AlreadyRecovered.diagnostic(LoanRefusalOperation::Recovery);
    assert_eq!(recovery.category(), LoanRefusalCategory::Recovery);
    let lifetime = LoanRefusal::ScopeEnded.diagnostic(LoanRefusalOperation::Transition);
    assert_eq!(lifetime.category(), LoanRefusalCategory::Lifetime);
    let arena = LoanRefusal::WrongArena.diagnostic(LoanRefusalOperation::Transition);
    assert_eq!(arena.category(), LoanRefusalCategory::WrongArena);
}

#[test]
fn refusal_diagnostic_is_a_small_bounded_payload() {
    assert!(std::mem::size_of::<LoanRefusalDiagnostic>() <= 512);
    let subject = LoanRefusalSubject::resource(memory(0, 4, true));
    let diagnostic =
        LoanRefusal::ActiveDependency.diagnostic_with_subject(LoanRefusalOperation::Plan, subject);
    assert!(diagnostic.subject().resource_fact().is_some());
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/loans/tests.rs");
}

#[test]
fn selected_loan_consumption_never_tries_another_occurrence() {
    let facts = PureFactContext::new();
    let first = memory(0, 4, true);
    let second = memory(4, 8, true);
    let (resources, occurrences) = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_facts_and_occurrences([first.clone(), second.clone()]);
    let mut origins = MemorySplitOrigins::default();
    assert!(
        resources
            .clone()
            .without_selected_fact_with_origins(occurrences[0].1, &second, &facts, &mut origins,)
            .is_none()
    );
    let consumed = resources
        .clone()
        .without_selected_fact_with_origins(occurrences[1].1, &second, &facts, &mut origins)
        .expect("the supplied occurrence owns the requested resource");
    assert!(consumed.contains_exact_representation(&first));
    assert!(!consumed.contains_exact_representation(&second));
    assert!(resources.contains_exact_representation(&second));
}

#[test]
fn indexed_write_witness_keeps_the_least_loan_across_buckets_and_aliases() {
    let (mut ledger, holder, _) = participants();
    let mut first = None;
    for (start, end) in [(12, 16), (0, 32), (64, 96)] {
        let view = memory(start, end, false);
        let resources = ResourceContext::new().unchecked_with_fact(view.clone());
        let opening = ledger
            .borrowed_contract_input(holder, resources.occurrences_for_fact(&view)[0], view, None)
            .unwrap();
        first.get_or_insert(opening.loan);
        ledger = ledger.apply(&opening.transition).unwrap();
    }
    for (start, end) in [(0, 32), (0, 1), (12, 16), (32, 64), (64, 100), (16, 16)] {
        let query = memory(start, end, false);
        let range = query.memory_range().unwrap();
        let expected = ledger
            .active_memory_overlaps(range)
            .unwrap()
            .first()
            .copied();
        assert_eq!(ledger.first_active_memory_overlap(range), Ok(expected));
        let report = ledger.memory_access_refusal(
            range,
            &PureFactContext::new(),
            LoanRefusalOperation::MemoryAccess,
        );
        assert_eq!(
            report.and_then(|d| d.subject().loan_id()),
            expected.map(|loan| (loan.arena, loan.ordinal))
        );
    }
    let original = memory(0, 32, false);
    let alias = Pointer {
        block: PointerBlock::Symbolic(Variable(991_123)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(
            alias.clone(),
            original.memory_range().unwrap().base().clone(),
        ),
        true,
    );
    let query = MemoryRange::new_with_element_width(
        alias,
        0u32.into(),
        32u32.into(),
        original.memory_range().unwrap().element_width(),
    );
    assert_eq!(
        ledger.first_active_memory_overlap_with_assumptions(&query, &facts),
        Ok(first)
    );
    assert_eq!(
        ledger
            .memory_access_refusal(&query, &facts, LoanRefusalOperation::MemoryAccess)
            .unwrap()
            .subject()
            .loan_id(),
        first.map(|loan| (loan.arena, loan.ordinal))
    );
    let unknown = parameter_range(991_124, 0, 1, 4);
    assert_eq!(
        ledger.first_active_memory_overlap(&unknown),
        Err(LoanRefusal::UnsupportedPartition)
    );
    assert_eq!(
        LoanLedger::new().first_active_memory_overlap(&unknown),
        Ok(None)
    );
}
