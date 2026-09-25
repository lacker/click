//! Checked operations on iterated guarded ownership (`CResource::Iterated`).
//!
//! The fact itself is defined in `primitives/iterated.rs`. Everything here
//! answers a question about one index or one C store, so each operation reads
//! the one fact it names, the index's range membership, the guard cell at that
//! index, and the fact's holes. Nothing enumerates the index range.
//!
//! The invariant every operation preserves: the fact holds, for each index
//! `k` of its range that is not a hole, the element at `k` exactly when the
//! guard at `k` holds in the *current* memory. The guard cells are owned
//! beside the fact (validation requires the body to own them), so only this
//! context can change them, and every change goes through
//! [`plan_iterated_guard_store`] or drops the fact.

use super::*;

/// The element-level proof steps and the whole-range conversions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IteratedStep {
    /// `take(base[a..b])`: move one element out of the fact.
    Take { element: CMemoryRange },
    /// `give(base[a..b])`: move one element back into the fact.
    Give { element: CMemoryRange },
    /// `gather(resource)`: form `template` (a hole-free fact) from the
    /// covering owned range when every guard is known true, or from nothing
    /// when every guard is known false.
    Gather { template: CIteratedMemory },
    /// `scatter(resource)`: the converse of `gather`.
    Scatter { template: CIteratedMemory },
}

/// Decides one condition from the fact context: `Some(true)`, `Some(false)`,
/// or `None` when neither is established.
fn decide(assumptions: &PureFactContext, condition: ConditionTerm) -> Option<bool> {
    crate::instrumentation::record_deterministic_work(1);
    assumptions.decide(&condition)
}

fn proves(assumptions: &PureFactContext, condition: ConditionTerm) -> bool {
    decide(assumptions, condition) == Some(true)
}

fn terms_equal(
    assumptions: &PureFactContext,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    left == right
        || proves(
            assumptions,
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
        )
}

fn terms_distinct(
    assumptions: &PureFactContext,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    left != right
        && decide(
            assumptions,
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone())),
        ) == Some(false)
}

fn pointers_equal(assumptions: &PureFactContext, left: &Pointer, right: &Pointer) -> bool {
    left == right || assumptions.pointers_proven_equal_ignoring_memory_separation(left, right)
}

/// Whether `index` lies in the fact's range, by the fact context.
fn index_in_range(
    assumptions: &PureFactContext,
    iterated: &CIteratedMemory,
    index: &Bitvector32Term,
) -> bool {
    proves(
        assumptions,
        ConditionTerm::signed_less_equal(iterated.lower().clone(), index.clone()),
    ) && proves(
        assumptions,
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(index.clone()),
            Box::new(iterated.upper().clone()),
        ),
    )
}

/// Whether `index` lies outside the fact's range, by the fact context.
fn index_out_of_range(
    assumptions: &PureFactContext,
    iterated: &CIteratedMemory,
    index: &Bitvector32Term,
) -> bool {
    proves(
        assumptions,
        ConditionTerm::Bitvector32SignedLessThan(
            Box::new(index.clone()),
            Box::new(iterated.lower().clone()),
        ),
    ) || proves(
        assumptions,
        ConditionTerm::signed_less_equal(iterated.upper().clone(), index.clone()),
    )
}

/// The guard's truth for a guard cell holding `cell`.
fn guard_holds_for(
    assumptions: &PureFactContext,
    iterated: &CIteratedMemory,
    cell: &Bitvector32Term,
) -> Option<bool> {
    let equal = decide(
        assumptions,
        ConditionTerm::Bitvector32Equal(
            Box::new(cell.clone()),
            Box::new(iterated.guard().value().clone()),
        ),
    )?;
    Some(equal == iterated.guard().holds_when_equal())
}

/// The logical guard value in this snapshot. Gathering ownership does not
/// execute a C read: it needs the guard's truth, while the surrounding rule
/// separately requires ownership of the guard range. A logical value fact
/// never establishes that a subsequent C load is initialized.
fn guard_cell_value(
    state: &CState,
    iterated: &CIteratedMemory,
    index: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Result<Bitvector32Term, String> {
    let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
        state.memory(),
        iterated.guard_cell(index),
        iterated.guard().cell_type,
        Vec::new(),
        Vec::new(),
        assumptions,
    );
    match paths.as_slice() {
        [
            CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Int32(value)),
                facts,
                obligations,
            },
        ] if facts
            .iter()
            .all(|fact| assumptions.proves_exact(fact.proposition()))
            && obligations.is_empty() =>
        {
            Ok(value.clone())
        }
        _ => Err("the iterated guard does not denote one logical int32 value".into()),
    }
}

/// The guard's truth at `index` in `state`: `Some(true)` when the fact
/// context proves it holds, `Some(false)` when it proves it fails, and
/// `None` when neither is established.
pub(crate) fn iterated_guard_at(
    state: &CState,
    iterated: &CIteratedMemory,
    index: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Result<Option<bool>, String> {
    let cell = guard_cell_value(state, iterated, index, assumptions)?;
    Ok(guard_holds_for(assumptions, iterated, &cell))
}

/// Whether the fact holds the element at `index`: `Some(true)` when the index
/// is in range, not a hole, and its guard is known true; `Some(false)` when
/// the index is out of range, a hole, or its guard is known false; `None`
/// ("may hold") otherwise. This is the containment and separation question
/// for one element, answered from one guard cell and the holes.
pub(crate) fn iterated_holds_element(
    state: &CState,
    iterated: &CIteratedMemory,
    index: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Option<bool> {
    if index_out_of_range(assumptions, iterated, index)
        || iterated
            .holes()
            .iter()
            .any(|hole| terms_equal(assumptions, hole, index))
    {
        return Some(false);
    }
    let guard = iterated_guard_at(state, iterated, index, assumptions).ok()?;
    match guard {
        Some(false) => Some(false),
        Some(true)
            if index_in_range(assumptions, iterated, index)
                && iterated
                    .holes()
                    .iter()
                    .all(|hole| terms_distinct(assumptions, hole, index)) =>
        {
            Some(true)
        }
        _ => None,
    }
}

/// Whether the fact is proved to hold nothing in `range`: the range is in
/// another block, or the element block's elements of the fact lie entirely
/// outside it by constant bounds. Constant in the fact's range size.
pub(crate) fn iterated_separate_from_range(
    iterated: &CIteratedMemory,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if range.base().blocks_proven_distinct(iterated.element_base()) {
        return true;
    }
    let Some(covering) = iterated.covering_range().or_else(|| {
        // Gapped elements are covered by the range from the first element's
        // start to the last element's end.
        let first = iterated.element_range(iterated.lower());
        let last = iterated.element_range(&Bitvector32Term::subtract(
            iterated.upper().clone(),
            Bitvector32Term::Constant(1),
        ));
        Some(CMemoryRange::new_with_element_width(
            iterated.element_base().clone(),
            first.start().clone(),
            last.end().clone(),
            iterated.element_width(),
        ))
    }) else {
        return false;
    };
    assumptions.proves_resource_separate(
        &CResource::Memory(covering),
        &CResource::Memory(range.clone()),
    )
}

fn owned_iterated_candidates(
    resources: &ResourceContext,
    block: PointerBlock,
) -> impl Iterator<Item = (&CResourceFact, &CIteratedMemory)> {
    resources
        .iterated_facts_in_block(&block)
        .filter_map(move |fact| match fact {
            CResourceFact::Own(CResource::Iterated(iterated), quantity)
                if quantity.as_const() == Some(1) && iterated.element_base().block == block =>
            {
                Some((fact, iterated.as_ref()))
            }
            _ => None,
        })
}

/// The one owned iterated fact whose elements live at `element`'s base.
fn iterated_fact_for_element<'a>(
    resources: &'a ResourceContext,
    element: &CMemoryRange,
    assumptions: &PureFactContext,
) -> Result<(&'a CResourceFact, &'a CIteratedMemory), String> {
    let mut found = None;
    for (fact, iterated) in owned_iterated_candidates(resources, element.base().block.clone()) {
        if iterated.element_width() != element.element_width()
            || !pointers_equal(assumptions, iterated.element_base(), element.base())
        {
            continue;
        }
        if found.replace((fact, iterated)).is_some() {
            return Err("two iterated ownership facts share this element base".to_string());
        }
    }
    found.ok_or_else(|| {
        "no iterated ownership fact holds elements at this base; `unfold` the resource that declares it first"
            .to_string()
    })
}

/// The index whose element `element` claims to be: its start with the
/// clause's constant offset removed and, for a stride above one, the stride
/// factored out of the term as written. [`check_element_at`] then decides
/// that the whole range is that element.
fn element_index(
    iterated: &CIteratedMemory,
    element: &CMemoryRange,
) -> Result<Bitvector32Term, String> {
    let scaled = Bitvector32Term::subtract(
        element.start().clone(),
        Bitvector32Term::Constant(iterated.start_offset as u32),
    );
    if iterated.stride == 1 {
        return Ok(scaled);
    }
    let stride = Bitvector32Term::Constant(iterated.stride);
    match &scaled {
        Bitvector32Term::Multiply(left, right) if right.as_ref() == &stride => {
            Ok(left.as_ref().clone())
        }
        Bitvector32Term::Multiply(left, right) if left.as_ref() == &stride => {
            Ok(right.as_ref().clone())
        }
        _ => Err(format!(
            "write the element as `base[{} * index + {}..]`, the clause's own shape",
            iterated.stride, iterated.start_offset
        )),
    }
}

/// Checks that `element` is exactly the fact's element at `index`.
fn check_element_at(
    iterated: &CIteratedMemory,
    element: &CMemoryRange,
    index: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let expected = iterated.element_range(index);
    if terms_equal(assumptions, element.start(), expected.start())
        && terms_equal(assumptions, element.end(), expected.end())
    {
        Ok(())
    } else {
        Err("the range is not one element of the iterated ownership fact".to_string())
    }
}

fn replace_iterated(
    resources: ResourceContext,
    current: &CResourceFact,
    next: CIteratedMemory,
) -> Result<ResourceContext, String> {
    resources
        .without_exact_representation(current)
        .map(|resources| {
            resources.unchecked_with_fact(CResourceFact::own(CResource::iterated(next)))
        })
        .ok_or_else(|| "the iterated ownership fact is not held".to_string())
}

/// Applies one checked iterated-ownership step to `state`. Each step reads
/// the one fact it names, one guard cell, the fact's holes, and the element
/// it moves; the index range is never enumerated.
pub(crate) fn apply_iterated_step(
    state: &CState,
    step: &IteratedStep,
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    match step {
        IteratedStep::Take { element } => {
            let (current, iterated) =
                iterated_fact_for_element(state.resources(), element, assumptions)?;
            let index = &element_index(iterated, element)?;
            check_element_at(iterated, element, index, assumptions)?;
            if !index_in_range(assumptions, iterated, index) {
                return Err(
                    "the index is not known to lie in the iterated range; establish `lo <= index` and `index < hi` first"
                        .to_string(),
                );
            }
            if let Some(hole) = iterated
                .holes()
                .iter()
                .find(|hole| !terms_distinct(assumptions, hole, index))
            {
                let _ = hole;
                return Err(
                    "this element may already be taken out: the index is not known to differ from an element taken out earlier"
                        .to_string(),
                );
            }
            match iterated_guard_at(state, iterated, index, assumptions)? {
                Some(true) => {}
                Some(false) => {
                    return Err(
                        "the guard is false at this index, so the iterated ownership fact holds no element there"
                            .to_string(),
                    );
                }
                None => {
                    return Err(
                        "the guard at this index is not known to hold; state the guard cell's value as a fact first"
                            .to_string(),
                    );
                }
            }
            let next = iterated.with_hole(index.clone());
            let resources = replace_iterated(state.resources().clone(), current, next)?;
            let resources = resources
                .try_compose_with_facts([CResourceFact::own_memory(element.clone())], assumptions)
                .map_err(|_| "the element overlaps memory this context already owns".to_string())?;
            Ok(state.clone().with_resource_context(resources))
        }
        IteratedStep::Give { element } => {
            let (current, iterated) =
                iterated_fact_for_element(state.resources(), element, assumptions)?;
            let index = &element_index(iterated, element)?;
            check_element_at(iterated, element, index, assumptions)?;
            match iterated_guard_at(state, iterated, index, assumptions)? {
                Some(true) => {}
                Some(false) => {
                    return Err(
                        "the guard is false at this index, so the iterated ownership fact cannot hold the element; set the guard cell first"
                            .to_string(),
                    );
                }
                None => {
                    return Err(
                        "the guard at this index is not known to hold; state the guard cell's value as a fact first"
                            .to_string(),
                    );
                }
            }
            let Some(position) = iterated
                .holes()
                .iter()
                .position(|hole| terms_equal(assumptions, hole, index))
            else {
                return Err(
                    "this element was not taken out of the iterated ownership fact; only an element taken out, or whose guard a store just made true, can be given back"
                        .to_string(),
                );
            };
            let next = iterated.without_hole_at(position);
            let resources = state
                .resources()
                .clone()
                .without_fact(&CResourceFact::own_memory(element.clone()), assumptions)
                .ok_or_else(|| "the element is not owned here".to_string())?;
            let resources = replace_iterated(resources, current, next)?;
            Ok(state.clone().with_resource_context(resources))
        }
        IteratedStep::Gather { template } => {
            if !template.holes().is_empty() {
                return Err("a gathered iterated fact has no elements taken out".to_string());
            }
            // The guard is read against cells this context owns, exactly as
            // a declaration's guard reads cells its own body owns; otherwise
            // someone else could change which elements the fact claims.
            if !state.resources().satisfies_fact(
                &CResourceFact::own_memory(template.guard_range()),
                assumptions,
            ) {
                return Err(
                    "gathering needs ownership of every guard cell of the range".to_string()
                );
            }
            match every_guard(state, template, assumptions)? {
                Some(true) => {
                    let covering = template.covering_range().ok_or_else(|| {
                        "the elements do not tile one range, so they cannot be gathered from one"
                            .to_string()
                    })?;
                    let resources = state
                        .resources()
                        .clone()
                        .without_fact(&CResourceFact::own_memory(covering), assumptions)
                        .ok_or_else(|| {
                            "gathering needs ownership of every element's cells".to_string()
                        })?;
                    Ok(state.clone().with_resource_context(resources.unchecked_with_fact(
                        CResourceFact::own(CResource::iterated(template.clone())),
                    )))
                }
                Some(false) => Ok(state.clone().with_resource_context(
                    state.resources().clone().unchecked_with_fact(CResourceFact::own(
                        CResource::iterated(template.clone()),
                    )),
                )),
                None => Err(
                    "gathering needs every guard known: a fact `forall (k: int32) { lo <= k and k < hi implies guard }` or its negation"
                        .to_string(),
                ),
            }
        }
        IteratedStep::Scatter { template } => {
            let required = CResourceFact::own(CResource::iterated(template.clone()));
            let resources = state
                .resources()
                .clone()
                .without_fact(&required, assumptions)
                .ok_or_else(|| {
                    "scattering needs the iterated ownership fact with no element taken out"
                        .to_string()
                })?;
            match every_guard(state, template, assumptions)? {
                Some(true) => {
                    let covering = template.covering_range().ok_or_else(|| {
                        "the elements do not tile one range, so they cannot be scattered into one"
                            .to_string()
                    })?;
                    let resources = resources
                        .try_compose_with_facts([CResourceFact::own_memory(covering)], assumptions)
                        .map_err(|_| {
                            "the elements overlap memory this context already owns".to_string()
                        })?;
                    Ok(state.clone().with_resource_context(resources))
                }
                Some(false) => Ok(state.clone().with_resource_context(resources)),
                None => Err(
                    "scattering needs every guard known: a fact `forall (k: int32) { lo <= k and k < hi implies guard }` or its negation"
                        .to_string(),
                ),
            }
        }
    }
}

/// The reserved identity of the arbitrary index `gather` and `scatter`
/// instantiate the range's guard at. It is bound only inside the one
/// hypothetical fact context those checks build.
const ITERATED_GUARD_INDEX: Variable = Variable(u64::MAX - 0x6974_6572);

/// Whether every guard of the range is known true (`Some(true)`) or known
/// false (`Some(false)`): the universally quantified guard at a fresh index is
/// instantiated once and decided under the range hypotheses. One decision,
/// independent of the range's size.
fn every_guard(
    state: &CState,
    iterated: &CIteratedMemory,
    assumptions: &PureFactContext,
) -> Result<Option<bool>, String> {
    let index = Bitvector32Term::Variable(ITERATED_GUARD_INDEX);
    let hypotheses = assumptions
        .clone()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(iterated.lower().clone(), index.clone()),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(index.clone()),
                Box::new(iterated.upper().clone()),
            ),
            true,
        ));
    let cell = guard_cell_value(state, iterated, &index, &hypotheses)?;
    if let Some(value) = guard_holds_for(&hypotheses, iterated, &cell) {
        return Ok(Some(value));
    }
    // The guard over the whole range is a universally quantified fact;
    // instantiating it at the arbitrary index is the one scan over the
    // context's quantified facts this whole-range step makes.
    let instantiated = instantiate_guard(&hypotheses, iterated, &cell);
    Ok(guard_holds_for(&instantiated, iterated, &cell))
}

/// `hypotheses` with every universally quantified fact instantiated at the
/// guard comparison of `cell`.
fn instantiate_guard(
    hypotheses: &PureFactContext,
    iterated: &CIteratedMemory,
    cell: &Bitvector32Term,
) -> PureFactContext {
    let equal = ConditionTerm::Bitvector32Equal(
        Box::new(cell.clone()),
        Box::new(iterated.guard().value().clone()),
    );
    hypotheses
        .instantiated_universal_consequents(&equal)
        .into_iter()
        .fold(hypotheses.clone(), |facts, consequent| {
            facts.assume_proposition(consequent)
        })
}

/// The frame of a loop that declares its own resources, without the iterated
/// facts whose guard cells the loop may write. The body executes without
/// those facts (a declaring loop's body holds only what it declares), so no
/// store in it passes the store rule for them; after the loop the guard
/// cells may hold anything, and a fact read against them would claim cells
/// nobody checked. Dropping the fact is the sound answer: the elements are
/// lost to this frame, never claimed twice.
pub(crate) fn frame_out_iterated_facts_written_by_loop(
    state: CState,
    written: Option<&[CMemoryRange]>,
) -> CState {
    if !state.resources().has_iterated_facts() {
        return state;
    }
    let mut resources = state.resources().clone();
    for fact in state.resources().iterated_facts() {
        let CResource::Iterated(iterated) = fact.resource() else {
            continue;
        };
        let guard_block = &iterated.guard().base().block;
        let written_here = written.is_none_or(|ranges| {
            ranges.iter().any(|range| {
                &range.base().block == guard_block
                    || !range.base().block.proven_distinct(guard_block)
                        && (range.base().has_symbolic_block()
                            || iterated.guard().base().has_symbolic_block())
            })
        });
        if written_here && let Some(next) = resources.clone().without_exact_representation(&fact) {
            resources = next;
        }
    }
    state.with_resource_context(resources)
}

/// What a C store to `pointer` does to the iterated facts whose guard cells
/// share its block: for each fact, the representation to hold while the store
/// writes and the one to hold after it.
pub(crate) struct IteratedStorePlan {
    replacements: Vec<(CResourceFact, CIteratedMemory, CIteratedMemory)>,
}

impl IteratedStorePlan {
    /// The resource context with every affected fact in its during-store
    /// form: the stored index is a hole, so the store changes nothing the
    /// fact claims.
    pub(crate) fn before_store(
        &self,
        resources: ResourceContext,
    ) -> Result<ResourceContext, String> {
        self.replacements
            .iter()
            .try_fold(resources, |resources, (current, during, _)| {
                replace_iterated(resources, current, during.clone())
            })
    }

    /// The resource context with every affected fact in its after-store form.
    pub(crate) fn after_store(
        &self,
        resources: ResourceContext,
    ) -> Result<ResourceContext, String> {
        self.replacements
            .iter()
            .try_fold(resources, |resources, (_, during, after)| {
                if during == after {
                    return Ok(resources);
                }
                replace_iterated(
                    resources,
                    &CResourceFact::own(CResource::iterated(during.clone())),
                    after.clone(),
                )
            })
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.replacements.is_empty()
    }
}

/// The store rule. A store of `value` to `pointer` may change a guard cell,
/// and so change which elements an iterated fact claims. It is permitted at
/// index `j` exactly when
///
/// - `j` is outside the fact's range, or
/// - `j` is a hole (its element was taken out), or
/// - the guard at `j` is known false before the store, or the element at `j`
///   is owned outright beside the fact (either way the fact holds nothing at
///   `j`).
///
/// In every permitted case the fact makes no claim at `j` while the store
/// writes, so the store cannot change what it holds. After the store `j`
/// stays a hole unless it is out of range or the stored value makes the guard
/// known false; a store that makes the guard true therefore leaves `j` a hole
/// until `give` returns the element. A store at an index whose element the
/// fact may still hold is refused: it would silently change the fact.
pub(crate) fn plan_iterated_guard_store(
    state: &CState,
    pointer: &Pointer,
    value: &CValue,
    assumptions: &PureFactContext,
) -> Result<IteratedStorePlan, String> {
    let resources = state.resources();
    let mut replacements = Vec::new();
    if !resources.has_iterated_facts() {
        return Ok(IteratedStorePlan { replacements });
    }
    for fact in resources.iterated_facts_in_block(&pointer.block) {
        let CResourceFact::Own(CResource::Iterated(iterated), _) = fact else {
            continue;
        };
        if iterated.guard().base().block != pointer.block {
            continue;
        }
        // Owned memory is a partition: a cell one owned range authorizes
        // cannot be a guard cell another owned range holds.
        let written = CResource::Memory(CMemoryRange::new_with_element_width(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
            value.byte_width().max(1),
        ));
        if resources.proves_owned_resources_separate(
            &written,
            &CResource::Memory(iterated.guard_range()),
            assumptions,
        ) {
            continue;
        }
        let refusal = |reason: &str| {
            format!(
                "this store may change a guard cell of the iterated ownership of `{}`, which would change the elements it holds: {reason}; `take` the element at this index first, or establish that its guard is false",
                iterated.owner()
            )
        };
        let Some(index) = pointer.element_index_from_base_with_width(
            iterated.guard().base(),
            iterated.guard().cell_width,
        ) else {
            return Err(refusal(
                "the stored address is not a guard cell Click can index",
            ));
        };
        if value.byte_width() != iterated.guard().cell_width {
            return Err(refusal("the store does not write one whole guard cell"));
        }
        let CValue::Int32(stored) = value else {
            return Err(refusal("the stored value is not an `int32`"));
        };
        let out_of_range = index_out_of_range(assumptions, iterated, &index);
        let hole = iterated
            .holes()
            .iter()
            .position(|hole| terms_equal(assumptions, hole, &index));
        let during = match hole {
            // Respell the hole as the stored index so the write's own
            // derivation names it structurally.
            Some(position) => iterated.without_hole_at(position).with_hole(index.clone()),
            None if out_of_range => iterated.with_hole(index.clone()),
            // The element is owned outright beside the fact. Owned memory is
            // a partition, so the fact cannot hold it: at this index it
            // claims nothing, whatever the guard cell says.
            None if resources.satisfies_fact(
                &CResourceFact::own_memory(iterated.element_range(&index)),
                assumptions,
            ) =>
            {
                iterated.with_hole(index.clone())
            }
            None => match iterated_holds_element(state, iterated, &index, assumptions) {
                Some(false) => iterated.with_hole(index.clone()),
                Some(true) => {
                    return Err(refusal(
                        "the guard holds at this index, so the fact still holds its element",
                    ));
                }
                None => {
                    return Err(refusal(
                        "the guard at this index is not known, so the fact may hold its element",
                    ));
                }
            },
        };
        let stored_guard = guard_holds_for(assumptions, iterated, stored);
        let after = if out_of_range || stored_guard == Some(false) {
            let position = during.holes().len() - 1;
            during.without_hole_at(position)
        } else {
            during.clone()
        };
        replacements.push((fact.clone(), during, after));
    }
    Ok(IteratedStorePlan { replacements })
}
