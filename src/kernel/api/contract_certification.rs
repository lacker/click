use super::*;

mod contract_claims;
pub use contract_claims::*;

/// Returns an exhaustive set of proof-only cases for undecided guards on
/// composite resources required directly at function entry.
///
/// A contract such as `owns nullable(p)` denotes either an empty resource or
/// its guarded body. Exact certification must check both meanings when the
/// caller leaves the guard symbolic, even if the C body contains no matching
/// `if`. The cases below are generated wholly from the kernel contract and
/// always include both truth values, so they add no trusted hypothesis.
pub(super) fn contract_resource_condition_cases(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
) -> Option<Vec<Vec<Proposition>>> {
    let entry_state = c_function_entry_state(caller_state, function, arguments)?;
    let mut budget = ExecutionBudget::default();
    let required_resources = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        assumptions,
        &mut budget,
    )
    .ok()?
    .ok()?;
    let mut guards = Vec::new();
    for resource in required_resources.facts() {
        let CResource::Composite {
            name,
            arguments: resource_arguments,
        } = resource.resource()
        else {
            continue;
        };
        let definition = function
            .composite_resource_definitions()
            .iter()
            .find(|definition| definition.name() == name)?;
        let Some(condition) = definition.condition() else {
            continue;
        };
        if definition.parameters().len() != resource_arguments.len() {
            return None;
        }
        let mut condition_state = CState::new()
            .with_memory(entry_state.memory().clone())
            .with_resource_context(required_resources.clone());
        for (parameter, value) in definition.parameters().iter().zip(resource_arguments) {
            if parameter.c_type() != value.c_type() {
                return None;
            }
            condition_state.locals.set_typed(
                parameter.name().to_string(),
                value.clone(),
                parameter.c_type(),
            );
        }
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &condition_state,
            condition,
            None,
            &lowering_assumptions,
            &mut budget,
        )
        .ok()?;
        let [path] = paths.as_slice() else {
            return None;
        };
        if !path.obligations.iter().all(|obligation| {
            certification_proves_proposition(assumptions, obligation.proposition())
        }) {
            return None;
        }
        if !guards.contains(&path.proposition) {
            guards.push(path.proposition.clone());
        }
    }

    let mut cases = vec![Vec::new()];
    for guard in guards {
        let negated = negate_contract_case_proposition(&guard);
        let mut next = Vec::new();
        for facts in cases {
            let case_assumptions = assumptions_with_propositions(assumptions, &facts);
            if certification_proves_proposition(&case_assumptions, &guard)
                || certification_proves_proposition(&case_assumptions, &negated)
            {
                next.push(facts);
                continue;
            }
            let mut when_true = facts.clone();
            when_true.push(guard.clone());
            next.push(when_true);
            let mut when_false = facts;
            when_false.push(negated.clone());
            next.push(when_false);
        }
        budget.consume_paths(next.len()).ok()?;
        cases = next;
    }
    Some(cases)
}

fn negate_contract_case_proposition(proposition: &Proposition) -> Proposition {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            Proposition::ConditionIs(condition.clone(), !*value)
        }
        Proposition::Not(body) => body.as_ref().clone(),
        proposition => Proposition::Not(Box::new(proposition.clone())),
    }
}

/// Splits a proposition into its conjunct leaves.
fn proposition_conjuncts(proposition: &Proposition, into: &mut Vec<Proposition>) {
    match proposition {
        Proposition::And(left, right) => {
            proposition_conjuncts(left, into);
            proposition_conjuncts(right, into);
        }
        other => into.push(other.clone()),
    }
}

/// Converts a pointer offset to its size in bytes as a bitvector term.
fn pointer_offset_bytes(offset: &PointerOffsetTerm) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(value) => {
            u32::try_from(*value).ok().map(Bitvector32Term::Constant)
        }
        PointerOffsetTerm::Variable(_) => None,
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            pointer_offset_bytes(left)?,
            pointer_offset_bytes(right)?,
        )),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            let width = u32::try_from(*byte_width).ok()?;
            if width == 1 {
                Some(value.as_ref().clone())
            } else {
                Some(Bitvector32Term::multiply(
                    value.as_ref().clone(),
                    Bitvector32Term::Constant(width),
                ))
            }
        }
    }
}

/// The byte distance from `fact_offset` to `goal_offset` when the goal
/// offset extends the fact offset additively.
fn pointer_offset_byte_delta(
    goal_offset: &PointerOffsetTerm,
    fact_offset: &PointerOffsetTerm,
) -> Option<Bitvector32Term> {
    if goal_offset == fact_offset {
        return Some(Bitvector32Term::Constant(0));
    }
    if let PointerOffsetTerm::Add(left, right) = goal_offset {
        if left.as_ref() == fact_offset {
            return pointer_offset_bytes(right);
        }
        if right.as_ref() == fact_offset {
            return pointer_offset_bytes(left);
        }
    }
    None
}

/// Splits `term + c` into its base term and additive constant (0 when none).
fn split_additive_constant(term: &Bitvector32Term) -> (Bitvector32Term, u32) {
    match term {
        Bitvector32Term::Add(left, right) => {
            if let Bitvector32Term::Constant(value) = right.as_ref() {
                return (left.as_ref().clone(), *value);
            }
            if let Bitvector32Term::Constant(value) = left.as_ref() {
                return (right.as_ref().clone(), *value);
            }
            (term.clone(), 0)
        }
        _ => (term.clone(), 0),
    }
}

/// Certifies a loadability goal from an assumed wider loadable fact over the
/// same memory snapshot: the goal's base must sit at a provably in-bounds
/// byte offset within the fact's span.
pub fn loadable_covered_by_fact(assumptions: &Assumptions, goal: &Proposition) -> bool {
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
    } = goal
    else {
        return false;
    };
    let covered = assumptions.prop_facts.iter().any(|fact| {
        let Proposition::CMemoryLoadable {
            memory: fact_memory,
            base: fact_base,
            bytes: fact_bytes,
        } = fact
        else {
            return false;
        };
        if fact_base.block != base.block {
            return false;
        }
        // Loadability of a covering span transports across snapshot spelling
        // differences and recorded write effects just like an exact-range
        // fact does.
        if fact_memory != memory
            && !crate::kernel::reasoning::memory_range_still_available(fact_memory, memory, base)
            && !c_memories_canonically_equal(fact_memory, memory)
            && !c_memories_connected_by_effects(fact_memory, memory, assumptions)
        {
            return false;
        }
        let Some(delta_bytes) = pointer_offset_byte_delta(&base.offset, &fact_base.offset) else {
            return false;
        };
        let start = assumptions.simplify_bitvector_under_assumptions(&Bitvector32Term::Constant(0));
        let delta = assumptions.simplify_bitvector_under_assumptions(&delta_bytes);
        let end = assumptions.simplify_bitvector_under_assumptions(&Bitvector32Term::add(
            delta_bytes,
            bytes.clone(),
        ));
        let span = assumptions.simplify_bitvector_under_assumptions(fact_bytes);
        let starts_in_bounds = assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(start.clone(), delta.clone()),
            true,
        )) || assumptions.proves_order_condition_for_memory_resolution(
            &ConditionTerm::signed_less_equal(start, delta),
            true,
        );
        let ends_in_bounds = assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(end.clone(), span.clone()),
            true,
        )) || assumptions.proves_order_condition_for_memory_resolution(
            &ConditionTerm::signed_less_equal(end.clone(), span.clone()),
            true,
        ) || {
            // Strip a shared additive constant: `a + b <= x + c` follows
            // from `a <= x` when `b <= c`.
            let (end_base, end_shift) = split_additive_constant(&end);
            let (span_base, span_shift) = split_additive_constant(&span);
            (end_shift as i32) <= (span_shift as i32)
                && (assumptions.proves(&Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(end_base.clone(), span_base.clone()),
                    true,
                )) || assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(end_base, span_base),
                    true,
                ))
        };
        if starts_in_bounds && ends_in_bounds {
            return true;
        }
        // Byte-scaled bounds can overflow the arithmetic the order prover
        // handles; retry at element granularity when the goal width folds to
        // a constant.
        assumptions
            .simplify_bitvector_under_assumptions(bytes)
            .as_const()
            .is_some_and(|byte_width| {
                assumptions
                    .proves_loadable_cell_from_region(fact_base, fact_bytes, base, byte_width)
            })
    });
    if covered {
        crate::kernel::record_implicit_reasoning_provenance(assumptions, goal);
    }
    covered
}

/// Certifies a universally-quantified loadability side-obligation from
/// assumed loadable facts: the bound premises become facts about the free
/// bound variable, and the loadable body must then be covered by a wider
/// assumed span.
fn forall_loadable_covered_by_fact(assumptions: &Assumptions, goal: &Proposition) -> bool {
    let Proposition::ForAll {
        sort: Sort::CInt32 | Sort::Bitvector32,
        body,
        ..
    } = goal
    else {
        return false;
    };
    let mut premises = Vec::new();
    let mut conclusion = body.as_ref();
    while let Proposition::Implies(premise, rest) = conclusion {
        proposition_conjuncts(premise, &mut premises);
        conclusion = rest.as_ref();
    }
    if !matches!(conclusion, Proposition::CMemoryLoadable { .. }) {
        return false;
    }
    let premise_assumptions = assumptions_with_propositions(assumptions, &premises);
    loadable_covered_by_fact(&premise_assumptions, conclusion)
}

/// Certifies a quantified single-byte loadability obligation from an assumed
/// quantified fact that constrains a load of the same address under premises
/// the obligation also assumes. Facts enter assumptions only through
/// safety-checked lowering, so a stated fact about `load(p)` witnesses that
/// the first byte at `p` is loadable.
fn quantified_load_fact_certifies_loadable(assumptions: &Assumptions, goal: &Proposition) -> bool {
    fn implication_parts(body: &Proposition) -> (Vec<Proposition>, &Proposition) {
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            proposition_conjuncts(premise, &mut premises);
            conclusion = rest.as_ref();
        }
        (premises, conclusion)
    }
    let Proposition::ForAll { var, sort, body } = goal else {
        return false;
    };
    let (goal_premises, conclusion) = implication_parts(body);
    let Proposition::CMemoryLoadable { base, bytes, .. } = conclusion else {
        return false;
    };
    // A load of any width witnesses its first byte.
    if bytes.as_const() != Some(1) {
        return false;
    }
    assumptions.prop_facts.iter().any(|fact| {
        let Proposition::ForAll {
            var: fact_var,
            sort: fact_sort,
            body: fact_body,
        } = fact
        else {
            return false;
        };
        if fact_sort != sort {
            return false;
        }
        let renamed = substitute_bitvector_variable_in_proposition(
            fact_body,
            *fact_var,
            &Bitvector32Term::Variable(*var),
        );
        let (fact_premises, fact_conclusion) = implication_parts(&renamed);
        // The fact applies whenever its premises hold, so they must be among
        // the obligation's assumed premises.
        if !fact_premises.iter().all(|fact_premise| {
            goal_premises.iter().any(|goal_premise| {
                goal_premise == fact_premise
                    || propositions_alpha_equivalent(fact_premise, goal_premise)
            })
        }) {
            return false;
        }
        condition_fact_mentions_load_of(fact_conclusion, base, assumptions)
    })
}

/// True when a condition fact constrains a load of exactly this pointer, so
/// the fact witnesses that the pointer's first byte is loadable.
fn condition_fact_mentions_load_of(
    fact: &Proposition,
    base: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    fn collect_load_pointers(term: &Bitvector32Term, pointers: &mut Vec<Pointer>) {
        match term {
            Bitvector32Term::MemoryLoad(_, pointer) => pointers.push(pointer.as_ref().clone()),
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right) => {
                collect_load_pointers(left, pointers);
                collect_load_pointers(right, pointers);
            }
            _ => {}
        }
    }
    let Proposition::ConditionIs(condition, _) = fact else {
        return false;
    };
    let mut load_pointers = Vec::new();
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            collect_load_pointers(left, &mut load_pointers);
            collect_load_pointers(right, &mut load_pointers);
        }
        ConditionTerm::PointerOffsetEqual(_, _)
        | ConditionTerm::PointerEqual(_, _)
        | ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_) => {}
    }
    load_pointers.iter().any(|pointer| {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        canonicalize_pointer_loads(pointer, 0) == canonicalize_pointer_loads(base, 0)
            || pointers_proven_equal_for_memory_resolution(pointer, base, assumptions)
    })
}

/// The leaf form of the load-fact witness: a single-byte loadability goal is
/// certified by any assumed condition fact constraining a load of the same
/// pointer.
fn load_fact_certifies_loadable(assumptions: &Assumptions, goal: &Proposition) -> bool {
    let Proposition::CMemoryLoadable { base, bytes, .. } = goal else {
        return false;
    };
    if bytes.as_const() != Some(1) {
        return false;
    }
    assumptions
        .pure_facts()
        .iter()
        .any(|fact| condition_fact_mentions_load_of(fact, base, assumptions))
}

/// An instantiated int32 load from an already-certified quantified fact is
/// loadable whenever that fact's guard holds for the requested index. This is
/// the pointwise form used while lowering another quantified proposition: the
/// bound variable has become an ordinary symbolic variable and its guard is
/// already present in `assumptions`.
pub(in crate::kernel) fn quantified_int32_fact_certifies_loadable_cell(
    assumptions: &Assumptions,
    base: &Pointer,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }
    fn collect_shallow_term_variables(term: &Bitvector32Term, variables: &mut BTreeSet<Variable>) {
        match term {
            Bitvector32Term::Constant(_) => {}
            Bitvector32Term::Variable(variable) => {
                variables.insert(*variable);
            }
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                collect_shallow_term_variables(left, variables);
                collect_shallow_term_variables(right, variables);
            }
            Bitvector32Term::BitwiseNot(inner) => {
                collect_shallow_term_variables(inner, variables);
            }
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                collect_shallow_term_variables(then_term, variables);
                collect_shallow_term_variables(else_term, variables);
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                collect_shallow_term_variables(start, variables);
                collect_shallow_term_variables(end, variables);
                collect_shallow_term_variables(initial, variables);
                collect_shallow_term_variables(body, variables);
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                for argument in arguments {
                    collect_shallow_term_variables(argument, variables);
                }
            }
            // The memory snapshot may contain a large symbolic state. Only
            // variables outside nested loads can be the surrounding
            // quantified index. Variables in the loaded address belong to
            // the base expression (for example the owner parameter), not to
            // that index.
            Bitvector32Term::MemoryLoad(_, _) => {}
        }
    }

    fn collect_shallow_offset_variables(
        offset: &PointerOffsetTerm,
        variables: &mut BTreeSet<Variable>,
    ) {
        match offset {
            PointerOffsetTerm::Constant(_) => {}
            PointerOffsetTerm::Variable(variable) => {
                variables.insert(*variable);
            }
            PointerOffsetTerm::Add(left, right) => {
                collect_shallow_offset_variables(left, variables);
                collect_shallow_offset_variables(right, variables);
            }
            PointerOffsetTerm::Int32Scaled { value, .. } => {
                collect_shallow_term_variables(value, variables);
            }
        }
    }

    fn implication_parts(body: &Proposition) -> (Vec<Proposition>, &Proposition) {
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            proposition_conjuncts(premise, &mut premises);
            conclusion = rest.as_ref();
        }
        (premises, conclusion)
    }

    let mut target_variables = BTreeSet::new();
    if let PointerBlock::Symbolic(variable) = base.block {
        target_variables.insert(variable);
    }
    collect_shallow_offset_variables(&base.offset, &mut target_variables);
    let exact_binder_candidates = assumptions.prop_facts.iter().filter(
        |fact| matches!(fact, Proposition::ForAll { var, .. } if target_variables.contains(var)),
    );
    let renamed_binder_candidates = assumptions.prop_facts.iter().filter(
        |fact| matches!(fact, Proposition::ForAll { var, .. } if !target_variables.contains(var)),
    );
    exact_binder_candidates
        .chain(renamed_binder_candidates)
        .any(|fact| {
            if crate::instrumentation::deadline_exceeded() {
                return false;
            }
            let Proposition::ForAll {
                var: fact_var,
                sort: Sort::CInt32 | Sort::Bitvector32,
                body,
            } = fact
            else {
                return false;
            };
            let exact_target = target_variables.contains(fact_var).then_some(*fact_var);
            exact_target
                .into_iter()
                .chain(
                    target_variables
                        .iter()
                        .copied()
                        .filter(|target| target != fact_var),
                )
                .any(|target_var| {
                    if crate::instrumentation::deadline_exceeded() {
                        return false;
                    }
                    let renamed = (target_var != *fact_var).then(|| {
                        substitute_bitvector_variable_in_proposition(
                            body,
                            *fact_var,
                            &Bitvector32Term::Variable(target_var),
                        )
                    });
                    let instantiated = renamed.as_ref().unwrap_or(body.as_ref());
                    let (premises, conclusion) = implication_parts(instantiated);
                    let premises_hold = premises.iter().all(|premise| {
                        !crate::instrumentation::deadline_exceeded()
                            && matches!(premise, Proposition::ConditionIs(_, _))
                            && certification_proves_proposition(assumptions, premise)
                    });
                    premises_hold && condition_fact_mentions_load_of(conclusion, base, assumptions)
                })
        })
}

/// A checked universal fact that reads every int32 cell in a guarded prefix
/// certifies that complete prefix as loadable. This is the range form needed
/// after modular initialization helpers: their postcondition can expose the
/// value of each written cell without returning a separate ad-hoc permission
/// proposition.
pub(in crate::kernel) fn quantified_int32_fact_certifies_loadable_range(
    assumptions: &Assumptions,
    memory: &CMemory,
    base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    if crate::instrumentation::deadline_exceeded() {
        return false;
    }

    let element_count = match bytes {
        Bitvector32Term::Multiply(left, right) if right.as_const() == Some(4) => left.as_ref(),
        Bitvector32Term::Multiply(left, right) if left.as_const() == Some(4) => right.as_ref(),
        _ => return false,
    };

    fn conjunct_refs<'a>(proposition: &'a Proposition, output: &mut Vec<&'a Proposition>) {
        match proposition {
            Proposition::And(left, right) => {
                conjunct_refs(left, output);
                conjunct_refs(right, output);
            }
            proposition => output.push(proposition),
        }
    }

    fn implication_parts(body: &Proposition) -> (Vec<&Proposition>, &Proposition) {
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            conjunct_refs(premise, &mut premises);
            conclusion = rest.as_ref();
        }
        (premises, conclusion)
    }

    fn collect_loads<'a>(term: &'a Bitvector32Term, loads: &mut Vec<(&'a CMemory, &'a Pointer)>) {
        match term {
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                loads.push((memory, pointer));
            }
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                collect_loads(left, loads);
                collect_loads(right, loads);
            }
            Bitvector32Term::BitwiseNot(inner) => collect_loads(inner, loads),
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                collect_loads(then_term, loads);
                collect_loads(else_term, loads);
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                collect_loads(start, loads);
                collect_loads(end, loads);
                collect_loads(initial, loads);
                collect_loads(body, loads);
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                for argument in arguments {
                    collect_loads(argument, loads);
                }
            }
            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        }
    }

    fn condition_loads<'a>(
        proposition: &'a Proposition,
        loads: &mut Vec<(&'a CMemory, &'a Pointer)>,
    ) {
        let Proposition::ConditionIs(condition, _) = proposition else {
            return;
        };
        match condition {
            ConditionTerm::Bitvector32SignedLessThan(left, right)
            | ConditionTerm::Bitvector32SignedLessEqual(left, right)
            | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
            | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
            | ConditionTerm::Bitvector32Equal(left, right)
            | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
            | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
            | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
            | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
            | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
                collect_loads(left, loads);
                collect_loads(right, loads);
            }
            ConditionTerm::PointerOffsetEqual(_, _)
            | ConditionTerm::PointerEqual(_, _)
            | ConditionTerm::Constant(_)
            | ConditionTerm::Variable(_) => {}
        }
    }

    let guard_matches = |premises: &[&Proposition], target: &ConditionTerm| {
        premises.iter().any(|premise| {
            matches!(premise, Proposition::ConditionIs(condition, true)
                if condition == target || assumptions.condition_matches(condition, target))
        })
    };

    assumptions.prop_facts.iter().any(|fact| {
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        let Proposition::ForAll {
            var,
            sort: Sort::CInt32 | Sort::Bitvector32,
            body,
        } = fact
        else {
            return false;
        };
        let (premises, conclusion) = implication_parts(body);
        let index = Bitvector32Term::Variable(*var);
        let lower = ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone());
        let upper = ConditionTerm::signed_less_than(index.clone(), element_count.clone());
        if !guard_matches(&premises, &lower) || !guard_matches(&premises, &upper) {
            return false;
        }
        let mut loads = Vec::new();
        condition_loads(conclusion, &mut loads);
        loads.iter().any(|(load_memory, pointer)| {
            *load_memory == memory
                && pointer
                    .element_index_from_base(base)
                    .is_some_and(|load_index| load_index == index)
        })
    })
}

/// Certifies an existential requirement side-obligation (typically the
/// loadability safety of an existential requirement body): the witness of an
/// assumed existential over the same sort supplies the bound variable, its
/// body conjuncts become facts, and the obligation body must then certify
/// pointwise.
fn certification_proves_exists_obligation_from_facts(
    assumptions: &Assumptions,
    obligation: &Proposition,
) -> bool {
    let Proposition::Exists {
        var, sort, body, ..
    } = obligation
    else {
        return false;
    };
    let fact_candidates = assumptions.prop_facts.iter().cloned().collect::<Vec<_>>();
    fact_candidates.iter().any(|fact| {
        let Proposition::Exists {
            var: fact_var,
            sort: fact_sort,
            body: fact_body,
            ..
        } = fact
        else {
            return false;
        };
        if fact_sort != sort {
            return false;
        }
        let renamed = substitute_bitvector_variable_in_proposition(
            fact_body,
            *fact_var,
            &Bitvector32Term::Variable(*var),
        );
        let mut witness_facts = Vec::new();
        proposition_conjuncts(&renamed, &mut witness_facts);
        let witness_assumptions = assumptions_with_propositions(assumptions, &witness_facts);
        let mut goals = Vec::new();
        proposition_conjuncts(body, &mut goals);
        goals.iter().all(|goal| {
            certification_proves_proposition(&witness_assumptions, goal)
                || loadable_covered_by_fact(&witness_assumptions, goal)
                || quantified_load_fact_certifies_loadable(&witness_assumptions, goal)
                || load_fact_certifies_loadable(&witness_assumptions, goal)
                // Nested existentials recurse: the inner obligation matches
                // an inner assumed existential the same way.
                || certification_proves_exists_obligation_from_facts(&witness_assumptions, goal)
        })
    })
}

pub(super) fn c_function_contract_certification_assumptions(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    mut assumptions: Assumptions,
    selection_assumptions: &Assumptions,
) -> Option<Assumptions> {
    let mut entry_state = c_function_entry_state(caller_state, function, arguments)?;
    let mut budget = ExecutionBudget::default();
    // Entry facts derived from declared parameter spellings (for example
    // sized array parameters) carry loadability that is part of the calling
    // convention; assume them before lowering requirements so requirement
    // side-obligations can be certified against them.
    for fact in selection_assumptions.prop_facts.iter() {
        if matches!(fact, Proposition::CMemoryLoadable { .. }) {
            assumptions = assumptions.assume_proposition(fact.clone());
        }
        // Universally-quantified implications concluding in an opaque
        // predicate are surface-verified theorem facts. The predicate has no
        // kernel definition, so the surface verifier is their authority,
        // like the loadability calling convention above.
        if quantified_predicate_implication_fact(fact) {
            assumptions = assumptions.assume_proposition(fact.clone());
        }
    }
    let mut requirement_obligations = Vec::new();
    for requirement in function.contract_requires() {
        let lowering_assumptions = assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads();
        let paths = match lower_spec_proposition_at_state_with_loop_entry(
            &entry_state,
            requirement,
            None,
            &lowering_assumptions,
            &mut budget,
        ) {
            Ok(paths) => paths,
            Err(limit) => {
                if crate::instrumentation::enabled() {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::Diagnostic(format!(
                            "contract requirement lowering hit {limit:?} for {}",
                            function.name()
                        )),
                    );
                }
                return None;
            }
        };
        let path = if let [path] = paths.as_slice() {
            path
        } else {
            let selection_context =
                assumptions_with_propositions(&assumptions, &selection_assumptions.pure_facts());
            let proposition_matches = paths
                .iter()
                .filter(|path| {
                    certification_proves_proposition(&selection_context, &path.proposition)
                })
                .collect::<Vec<_>>();
            if let [path] = proposition_matches.as_slice() {
                *path
            } else {
                let consistent = paths
                    .iter()
                    .filter(|path| {
                        !assumptions_with_propositions(
                            &selection_context,
                            &path
                                .facts
                                .iter()
                                .map(|fact| fact.proposition().clone())
                                .collect::<Vec<_>>(),
                        )
                        .is_inconsistent()
                    })
                    .collect::<Vec<_>>();
                let [path] = consistent.as_slice() else {
                    if crate::instrumentation::enabled() {
                        crate::instrumentation::emit(
                            crate::instrumentation::VerificationEvent::Diagnostic(format!(
                                "contract requirement for {} lowered to {} paths; {} matched the selected surface facts and {} remained consistent",
                                function.name(),
                                paths.len(),
                                proposition_matches.len(),
                                consistent.len(),
                            )),
                        );
                    }
                    return None;
                };
                *path
            }
        };
        for obligation in &path.obligations {
            if !requirement_obligations.contains(obligation) {
                requirement_obligations.push(obligation.clone());
            }
        }
        for fact in &path.facts {
            assumptions = assumptions.assume_proposition(fact.proposition().clone());
        }
        assumptions = assumptions.assume_proposition(path.proposition.clone());
    }
    let required_resources = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        &assumptions,
        &mut budget,
    )
    .ok()
    .and_then(Result::ok);
    let required_resources = required_resources?;
    let expanded = expand_all_composite_resource_facts_and_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    );
    let (_, resource_definition_facts) = expanded?;
    for proposition in resource_definition_facts {
        assumptions = assumptions.assume_proposition(proposition);
    }
    let population_facts = evaluate_resource_population_fact_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        &entry_state,
        &assumptions,
        false,
    )?;
    for proposition in population_facts {
        assumptions = assumptions.assume_proposition(proposition);
    }
    let expanded_required_resources = expand_all_composite_resource_facts(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    )?;
    let mut entry_resources = entry_state.resources().clone().normalized(&assumptions);
    let mut missing = Vec::new();
    for (index, required) in expanded_required_resources.facts().iter().enumerate() {
        let exposed = expose_composite_resource_fact(
            &entry_resources,
            required,
            function.composite_resource_definitions(),
            entry_state.memory(),
            &assumptions,
        )
        .or_else(|| {
            let CResource::Memory(required_range) = required.resource() else {
                return None;
            };
            let has_same_base = entry_resources.facts().iter().any(|available| {
                let CResource::Memory(available_range) = available.resource() else {
                    return false;
                };
                crate::kernel::assumptions::pointers_equal_ignoring_memories(
                    available_range.base(),
                    required_range.base(),
                )
            });
            (has_same_base && entry_resources.satisfies_fact(required, &assumptions))
                .then(|| entry_resources.clone())
        });
        let Some(exposed) = exposed else {
            missing.push((index, required));
            continue;
        };
        entry_resources = exposed;
    }
    if !missing.is_empty() {
        if crate::instrumentation::enabled() {
            let missing = missing
                .into_iter()
                .map(|(index, required)| {
                    let kind = match required.resource() {
                        CResource::Memory(range) => {
                            format!("memory in {}", range.base().block)
                        }
                        CResource::Composite { name, .. } => format!("composite {name}"),
                        CResource::Token { name, .. } => format!("token {name}"),
                    };
                    format!("{index}: {kind}")
                })
                .collect::<Vec<_>>();
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                format!(
                    "contract entry resources do not satisfy requirements ({}/{}, missing {})",
                    entry_resources.facts().len(),
                    expanded_required_resources.facts().len(),
                    missing.join(", ")
                ),
            ));
        }
        return None;
    }
    if !requirement_obligations.iter().all(|obligation| {
        // Definedness travels with the assumption. A heap-dependent
        // `requires` cannot be true in a state where its loads do not
        // denote, so assuming the requirement already entails the
        // loadability its evaluation needed: the caller had to establish
        // the requirement, and the same obligations are proof obligations
        // on the caller's side (see the path-obligation check in
        // `prepare_function_claim_path`, which does not exempt them).
        //
        // Only assumable obligations — the definedness kind — ride along.
        // A genuine verification condition still has to be discharged here.
        if obligation.is_assumable() {
            return true;
        }

        certification_proves_proposition(&assumptions, obligation.proposition())
            || resources_certify_loadability(
                &entry_state,
                &entry_resources,
                obligation.proposition(),
                &assumptions,
            )
            || loadable_covered_by_fact(&assumptions, obligation.proposition())
            || forall_loadable_covered_by_fact(&assumptions, obligation.proposition())
            || certification_proves_exists_obligation_from_facts(
                &assumptions,
                obligation.proposition(),
            )
    }) {
        if crate::instrumentation::enabled() {
            crate::instrumentation::emit(crate::instrumentation::VerificationEvent::Diagnostic(
                "contract entry resources do not certify requirement safety".to_string(),
            ));
        }
        return None;
    }
    for obligation in requirement_obligations {
        assumptions = assumptions.assume_proposition(obligation.proposition().clone());
    }
    for proposition in entry_resources.observable_facts(&assumptions).ok()? {
        assumptions = assumptions.assume_proposition(proposition);
    }
    entry_state.resources = entry_resources.clone();
    Some(assumptions)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicCExecution {
    let existing = crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "verification variable collection",
        || {
            let mut existing = BTreeSet::new();
            collect_c_state_bitvector_variables(&state, &mut existing);
            collect_c_function_bitvector_variables(&function, &mut existing);
            for argument in &arguments {
                collect_c_expression_bitvector_variables(argument, &mut existing);
            }
            collect_assumption_variables(&assumptions, &mut existing);
            collect_execution_environment_variables(&environment, &mut existing);
            existing
        },
    );
    let mut variables =
        VerificationVariableGenerator::fresh_for(budget.next_verification_variable, existing);
    let paths = match crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "verification path execution",
        || {
            execute_c_function_verification_paths(
                &state,
                &function,
                &arguments,
                &assumptions,
                &environment,
                execution_semantics,
                &mut budget,
                &mut variables,
                prepare_contract_resources,
            )
        },
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = crate::instrumentation::measure_operation(
        function.name(),
        "independent kernel execution",
        "checked path theorem assembly",
        || {
            paths
                .into_iter()
                .map(|path| {
                    let effect_facts = memory_effect_execution_facts(&path.facts);
                    let facts = public_execution_pure_facts(&path.facts);
                    let proposition = Proposition::CFunctionVerifies {
                        state: state.clone(),
                        function: function.clone(),
                        arguments: arguments.clone(),
                        outcome: path.outcome,
                    };
                    let theorem = Theorem::new(wrap_proof_facts(
                        proposition,
                        &assumptions,
                        &facts,
                        &path.obligations,
                    ));
                    SymbolicCExecutionPath {
                        assumptions: assumptions.clone(),
                        facts,
                        effect_facts,
                        obligations: path.obligations,
                        theorem,
                    }
                })
                .collect()
        },
    );

    SymbolicCExecution { paths, limit: None }
}

pub fn c_function_execution_candidates_from_outcomes(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    paths: Vec<(
        CFunctionOutcome,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    )>,
) -> CFunctionExecutionCandidates {
    let paths = paths
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            let effect_facts = memory_effect_execution_facts(&facts);
            let facts = public_execution_pure_facts(&facts);
            CFunctionExecutionCandidate {
                outcome,
                facts,
                effect_facts,
                obligations,
            }
        })
        .collect();

    CFunctionExecutionCandidates {
        state,
        function,
        arguments,
        paths,
    }
}

pub fn prove_c_function_satisfies_specification_from_symbolic_path(
    function: CFunction,
    specification: CFunctionSpecification,
    path: &SymbolicCExecutionPath,
) -> Option<Theorem> {
    let mut proved = path.theorem().proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proved {
        premises.push(premise.as_ref().clone());
        proved = body;
    }
    let (state, proved_function, arguments, outcome, verifies) = match proved {
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, false),
        Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome, true),
        _ => return None,
    };
    if state != specification.state()
        || proved_function != &function
        || arguments != specification.arguments()
        || outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let conclusion = if verifies {
        Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        }
    } else {
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        }
    };
    let proposition = requires
        .into_iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement), Box::new(body))
        });
    Some(Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(proposition, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    ))
}

fn certified_function_path_parts<'a>(
    function: &CFunction,
    path: &'a SymbolicCExecutionPath,
) -> Option<(
    &'a CState,
    &'a [CExpression],
    &'a CFunctionOutcome,
    Assumptions,
)> {
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let (state, proved_function, arguments, outcome) = match proposition {
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        }
        | Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => (state, function, arguments, outcome),
        _ => return None,
    };
    if proved_function != function {
        return None;
    }
    let mut assumptions = path.assumptions.clone();
    assumptions = assumptions_with_propositions(
        &assumptions,
        &path
            .execution_facts()
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>(),
    );
    Some((state, arguments, outcome, assumptions))
}

fn resource_contexts_definitionally_equal(
    function: &CFunction,
    left_memory: &CMemory,
    left: &ResourceContext,
    right_memory: &CMemory,
    right: &ResourceContext,
    assumptions: &Assumptions,
) -> bool {
    resource_contexts_definitionally_equal_with_definitions(
        function.composite_resource_definitions(),
        left_memory,
        left,
        right_memory,
        right,
        assumptions,
    )
}

pub(in crate::kernel) fn resource_contexts_definitionally_equal_with_definitions(
    composite_resource_definitions: &[CCompositeResourceDefinition],
    left_memory: &CMemory,
    left: &ResourceContext,
    right_memory: &CMemory,
    right: &ResourceContext,
    assumptions: &Assumptions,
) -> bool {
    if left == right {
        return true;
    }
    let relation_facts = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: relation facts",
        || {
            [(left, left_memory), (right, right_memory)]
                .into_iter()
                .flat_map(|(resources, memory)| {
                    resources.facts().iter().filter_map(move |fact| {
                        matches!(fact.resource(), CResource::Composite { .. })
                            .then(|| {
                                evaluate_composite_resource_relation_propositions(
                                    fact,
                                    composite_resource_definitions,
                                    memory,
                                    assumptions,
                                )
                            })
                            .flatten()
                    })
                })
                .flatten()
                .collect::<Vec<_>>()
        },
    );
    let enriched_assumptions = assumptions_with_propositions(assumptions, &relation_facts);
    let assumptions = &enriched_assumptions;
    let _assumptions_memo_scope =
        crate::kernel::assumptions::AssumptionsIdScope::enter(assumptions);
    let facts_directly_match = |left: &CResourceFact, right: &CResourceFact| match (left, right) {
        (CResourceFact::Own(left, left_quantity), CResourceFact::Own(right, right_quantity))
            if left_quantity == right_quantity =>
        {
            crate::kernel::assumptions::resources_equal_ignoring_memories(left, right)
                && c_resources_directly_match(left, right, assumptions)
        }
        (CResourceFact::View(left), CResourceFact::View(right)) => {
            crate::kernel::assumptions::resources_equal_ignoring_memories(left, right)
                && c_resources_directly_match(left, right, assumptions)
        }
        _ => false,
    };
    let directly_equal = |left: &ResourceContext, right: &ResourceContext| {
        left.facts().iter().all(|fact| {
            right
                .direct_match_candidates(fact)
                .any(|available| facts_directly_match(available, fact))
                || right.satisfies_fact(fact, assumptions)
        }) && right.facts().iter().all(|fact| {
            left.direct_match_candidates(fact)
                .any(|available| facts_directly_match(available, fact))
                || left.satisfies_fact(fact, assumptions)
        })
    };
    let definitionally_covers =
        |available: &ResourceContext, required: &ResourceContext, memory: &CMemory| {
            required.facts().iter().all(|fact| {
                expose_composite_resource_fact(
                    available,
                    fact,
                    composite_resource_definitions,
                    memory,
                    assumptions,
                )
                .is_some()
            })
        };
    if crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: direct",
        || directly_equal(left, right),
    ) {
        return true;
    }
    if left_memory == right_memory
        && crate::instrumentation::measure_operation(
            "kernel",
            "resource context equality",
            "resource equality: same-memory definitions",
            || {
                (definitionally_covers(left, right, left_memory)
                    && definitionally_covers(right, left, left_memory))
                    || resource_contexts_definitionally_equivalent_by_consumption(
                        left,
                        right,
                        composite_resource_definitions,
                        left_memory,
                        assumptions,
                    )
            },
        )
    {
        return true;
    }
    let expanded_left = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: expand left",
        || {
            expand_all_composite_resource_facts(
                left,
                composite_resource_definitions,
                left_memory,
                assumptions,
            )
        },
    );
    let expanded_right = crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: expand right",
        || {
            expand_all_composite_resource_facts(
                right,
                composite_resource_definitions,
                right_memory,
                assumptions,
            )
        },
    );
    let Some(left) = expanded_left else {
        return false;
    };
    let Some(right) = expanded_right else {
        return false;
    };

    crate::instrumentation::measure_operation(
        "kernel",
        "resource context equality",
        "resource equality: expanded direct",
        || directly_equal(&left, &right),
    )
}

/// Extracts constant bounds `lo <= var < hi` from a universal premise made
/// exclusively of constant comparisons against `var`. Returns `None` when any
/// conjunct is not such a bound, so instantiating the conclusion stays sound.
fn constant_variable_bounds(var: Variable, premise: &Proposition) -> Option<(u32, u32)> {
    fn collect(
        var: Variable,
        premise: &Proposition,
        lo: &mut Option<u32>,
        hi: &mut Option<u32>,
    ) -> bool {
        let bound = Bitvector32Term::Variable(var);
        match premise {
            Proposition::And(left, right) => {
                collect(var, left, lo, hi) && collect(var, right, lo, hi)
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(left, right),
                true,
            ) if **right == bound => {
                let Bitvector32Term::Constant(value) = **left else {
                    return false;
                };
                if value > i32::MAX as u32 {
                    return false;
                }
                *lo = Some(lo.map_or(value, |current: u32| current.max(value)));
                true
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(left, right),
                true,
            ) if **left == bound => {
                let Bitvector32Term::Constant(value) = **right else {
                    return false;
                };
                if value > i32::MAX as u32 {
                    return false;
                }
                *hi = Some(hi.map_or(value, |current: u32| current.min(value)));
                true
            }
            _ => false,
        }
    }
    let mut lo = None;
    let mut hi = None;
    if !collect(var, premise, &mut lo, &mut hi) {
        return None;
    }
    Some((lo?, hi?))
}

const FORALL_INSTANTIATION_LIMIT: u32 = 16;

/// Evaluates a premise whose variables have been substituted away to a
/// constant truth value; `None` when it is not a closed constant condition.
fn constant_premise_value(premise: &Proposition) -> Option<bool> {
    match premise {
        Proposition::And(left, right) => {
            Some(constant_premise_value(left)? && constant_premise_value(right)?)
        }
        Proposition::ConditionIs(condition, expected) => {
            let holds = match condition {
                ConditionTerm::Constant(value) => *value,
                ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32) <= (*right as i32)
                }
                ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32) < (*right as i32)
                }
                ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32).checked_add(*right as i32).is_none()
                }
                _ => return None,
            };
            Some(holds == *expected)
        }
        _ => None,
    }
}

/// Instantiates finitely-bounded universal facts (`forall x. guards -> lo <=
/// x < hi -> P(x)` with small constant bounds) at every point in the bound,
/// so the certifier can use per-index conclusions the way an unfolded proof
/// does. Guard premises (such as overflow side conditions) must evaluate to
/// constant truth after substitution, or the point is skipped.
fn finite_forall_instantiations(facts: &[Proposition]) -> Vec<Proposition> {
    let mut instantiated = Vec::new();
    for fact in facts {
        let Proposition::ForAll {
            var,
            sort: Sort::CInt32 | Sort::Bitvector32,
            body,
        } = fact
        else {
            continue;
        };
        let mut premises = Vec::new();
        let mut conclusion = body.as_ref();
        while let Proposition::Implies(premise, rest) = conclusion {
            premises.push(premise.as_ref());
            conclusion = rest.as_ref();
        }
        let Some((lo, hi)) = premises
            .iter()
            .find_map(|premise| constant_variable_bounds(*var, premise))
        else {
            continue;
        };
        if hi <= lo || hi - lo > FORALL_INSTANTIATION_LIMIT {
            continue;
        }
        for value in lo..hi {
            let witness = Bitvector32Term::Constant(value);
            let premises_hold = premises.iter().all(|premise| {
                constant_variable_bounds(*var, premise).is_some()
                    || constant_premise_value(&substitute_bitvector_variable_in_proposition(
                        premise, *var, &witness,
                    )) == Some(true)
            });
            if premises_hold {
                instantiated.push(substitute_bitvector_variable_in_proposition(
                    conclusion, *var, &witness,
                ));
            }
        }
    }
    instantiated
}

/// Structural equality up to renaming of bound variables at every quantifier
/// depth; bound variables are freshened per lowering pass, so nested
/// quantified facts never match syntactically.
pub(crate) fn propositions_alpha_equivalent(left: &Proposition, right: &Proposition) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::Exists {
                var: left_var,
                sort: left_sort,
                body: left_body,
                ..
            },
            Proposition::Exists {
                var: right_var,
                sort: right_sort,
                body: right_body,
                ..
            },
        ) => {
            left_sort == right_sort && {
                let renamed = substitute_bitvector_variable_in_proposition(
                    left_body,
                    *left_var,
                    &Bitvector32Term::Variable(*right_var),
                );
                propositions_alpha_equivalent(&renamed, right_body)
            }
        }
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort && {
                let renamed = substitute_bitvector_variable_in_proposition(
                    left_body,
                    *left_var,
                    &Bitvector32Term::Variable(*right_var),
                );
                propositions_alpha_equivalent(&renamed, right_body)
            }
        }
        (Proposition::And(al, ar), Proposition::And(bl, br))
        | (Proposition::Or(al, ar), Proposition::Or(bl, br))
        | (Proposition::Implies(al, ar), Proposition::Implies(bl, br)) => {
            propositions_alpha_equivalent(al, bl) && propositions_alpha_equivalent(ar, br)
        }
        (Proposition::Not(a), Proposition::Not(b)) => propositions_alpha_equivalent(a, b),
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            left_value == right_value
                && condition_with_canonical_loads(left_condition)
                    .zip(condition_with_canonical_loads(right_condition))
                    .is_some_and(|(left, right)| left == right)
        }
        (
            Proposition::CMemoryLoadable {
                memory: left_memory,
                base: left_base,
                bytes: left_bytes,
            },
            Proposition::CMemoryLoadable {
                memory: right_memory,
                base: right_base,
                bytes: right_bytes,
            },
        ) => {
            canonicalize_pointer_loads(left_base, 0) == canonicalize_pointer_loads(right_base, 0)
                && canonicalize_atomic_loads(left_bytes)
                    == canonicalize_atomic_loads(right_bytes)
                // Loadability depends on the snapshot's blocks, not its
                // cached cell values.
                && left_memory.blocks == right_memory.blocks
        }
        _ => false,
    }
}

/// Collects one-point-rule witness candidates for an existential body: any
/// conjunct shaped `var == term` (on either side) pins the bound variable to
/// `term`, provided `term` does not itself mention the variable.
fn exists_equality_witness_candidates(
    var: Variable,
    body: &Proposition,
    candidates: &mut Vec<Bitvector32Term>,
) {
    match body {
        Proposition::And(left, right) => {
            exists_equality_witness_candidates(var, left, candidates);
            exists_equality_witness_candidates(var, right, candidates);
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            let bound = Bitvector32Term::Variable(var);
            for (side, other) in [(left, right), (right, left)] {
                let mentions_var = crate::kernel::reasoning::substitute_bitvector_variable(
                    other,
                    var,
                    &Bitvector32Term::Constant(0),
                ) != **other;
                if **side == bound && !mentions_var {
                    candidates.push((**other).clone());
                }
            }
        }
        _ => {}
    }
}

/// Proves an order condition against a constant by removing an additive
/// constant shift from the term side, when the assumptions prove the shifted
/// addition overflow-free (the executing code already checked it). For
/// example `x + 1 > 0` becomes `x >= 0` under `!AddOverflows(x, 1)`.
fn shifted_order_condition_proven(
    assumptions: &Assumptions,
    condition: &ConditionTerm,
    value: bool,
) -> bool {
    if !value {
        return false;
    }
    // Normalize to `left OP right` with OP in {<, <=}.
    let (left, right, strict) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => (left, right, true),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => (left, right, false),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => (right, left, true),
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => (right, left, false),
        _ => return false,
    };
    let overflow_free = |base: &Bitvector32Term, shift: u32| {
        // Any exact strict signed upper bound on `base` keeps `base + 1`
        // below overflow: the bound itself is an int32 and therefore at
        // most INT_MAX. This is the same direct increment certificate the
        // executor uses for `x < capacity` before evaluating `x + 1`.
        if shift == 1 && assumptions.has_exact_strict_upper_bound(base) {
            return true;
        }
        let exact = assumptions.proves_exact(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedAddOverflows(
                Box::new(base.clone()),
                Box::new(Bitvector32Term::Constant(shift)),
            ),
            false,
        )) || assumptions.proves_exact(&Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedAddOverflows(
                Box::new(Bitvector32Term::Constant(shift)),
                Box::new(base.clone()),
            ),
            false,
        ));
        if exact {
            return true;
        }
        // A recorded overflow fact may spell the operand through loads at a
        // different snapshot; compare canonically.
        let canonical_base = canonicalize_atomic_loads(base);
        let recorded = assumptions.condition_facts.iter().any(|(condition, value)| {
            !*value
                && match condition {
                    ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                        (matches!(right.as_ref(), Bitvector32Term::Constant(c) if *c == shift)
                            && canonicalize_atomic_loads(left) == canonical_base)
                            || (matches!(left.as_ref(), Bitvector32Term::Constant(c) if *c == shift)
                                && canonicalize_atomic_loads(right) == canonical_base)
                    }
                    _ => false,
                }
        });
        if recorded {
            return true;
        }
        // Overflow-freedom also follows from a proven bound keeping the
        // shifted sum inside the signed range.
        let signed_shift = shift as i32;
        if signed_shift > 0 {
            let le_bound = Bitvector32Term::Constant((i32::MAX - signed_shift) as u32);
            let le = ConditionTerm::signed_less_equal(base.clone(), le_bound);
            let lt_bound = Bitvector32Term::Constant((i32::MAX - signed_shift + 1) as u32);
            let lt = ConditionTerm::signed_less_than(base.clone(), lt_bound);
            assumptions.proves_exact(&Proposition::ConditionIs(le.clone(), true))
                || assumptions.proves_order_condition_for_memory_resolution(&le, true)
                || assumptions.proves_exact(&Proposition::ConditionIs(lt.clone(), true))
                || assumptions.proves_order_condition_for_memory_resolution(&lt, true)
        } else if signed_shift < 0 {
            let bound = Bitvector32Term::Constant((i32::MIN - signed_shift) as u32);
            let condition = ConditionTerm::signed_less_equal(bound, base.clone());
            assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), true))
                || assumptions.proves_order_condition_for_memory_resolution(&condition, true)
        } else {
            true
        }
    };
    // `a + 1 <= b` follows from `a < b` for any terms when `a + 1` is
    // provably overflow-free; this converts a strict requirement into the
    // non-strict spelling a successor produces.
    if !strict {
        let (base, shift) = split_additive_constant(left);
        if shift == 1 {
            // `a < b` alone implies both that `a + 1` cannot overflow
            // (`a < b <= i32::MAX`) and the goal `a + 1 <= b`.
            let strict_form = ConditionTerm::signed_less_than(base, right.as_ref().clone());
            if certification_proves_proposition(
                assumptions,
                &Proposition::ConditionIs(strict_form, true),
            ) {
                return true;
            }
        }
    }
    let shifted = match (left.as_ref(), right.as_ref()) {
        (shifted_term, Bitvector32Term::Constant(bound)) => {
            let (base, shift) = split_additive_constant(shifted_term);
            if shift == 0 || !overflow_free(&base, shift) {
                return false;
            }
            let Some(new_bound) = (*bound as i32).checked_sub(shift as i32) else {
                return false;
            };
            (base, Bitvector32Term::Constant(new_bound as u32), false)
        }
        (Bitvector32Term::Constant(bound), shifted_term) => {
            let (base, shift) = split_additive_constant(shifted_term);
            if shift == 0 || !overflow_free(&base, shift) {
                return false;
            }
            let Some(new_bound) = (*bound as i32).checked_sub(shift as i32) else {
                return false;
            };
            (Bitvector32Term::Constant(new_bound as u32), base, true)
        }
        _ => return false,
    };
    let (new_left, new_right, constant_on_left) = shifted;
    let condition = match (strict, constant_on_left) {
        (true, false) | (true, true) => ConditionTerm::signed_less_than(new_left, new_right),
        (false, _) => ConditionTerm::signed_less_equal(new_left, new_right),
    };
    certification_proves_proposition(assumptions, &Proposition::ConditionIs(condition, true))
}

/// Compares two range folds up to renaming of their bound accumulator and
/// item variables; bound variables are freshened per lowering pass.
fn range_folds_alpha_equivalent(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    let (
        Bitvector32Term::RangeFold {
            start: left_start,
            end: left_end,
            initial: left_initial,
            accumulator: left_accumulator,
            item: left_item,
            body: left_body,
        },
        Bitvector32Term::RangeFold {
            start: right_start,
            end: right_end,
            initial: right_initial,
            accumulator: right_accumulator,
            item: right_item,
            body: right_body,
        },
    ) = (left, right)
    else {
        return false;
    };
    left_start == right_start && left_end == right_end && left_initial == right_initial && {
        let renamed = crate::kernel::reasoning::substitute_bitvector_variable(
            &crate::kernel::reasoning::substitute_bitvector_variable(
                right_body,
                *right_accumulator,
                &Bitvector32Term::Variable(*left_accumulator),
            ),
            *right_item,
            &Bitvector32Term::Variable(*left_item),
        );
        renamed == **left_body
    }
}

/// Splits both offsets into non-constant atoms plus a constant shift,
/// resolves atoms whose scaled values equality facts pin to a constant, and
/// requires the remaining atoms to match pairwise. Runs the bounded constant
/// resolver once per atom at top level, never inside the resolution
/// recursion.
fn pointer_offsets_equal_with_resolved_atoms(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
) -> bool {
    let resolve = |offset: &PointerOffsetTerm| {
        let (atoms, mut constant) = crate::kernel::reasoning::offset_atoms_and_constant(offset);
        let mut unresolved = Vec::new();
        for atom in atoms {
            if let PointerOffsetTerm::Int32Scaled { value, byte_width } = &atom
                && let Some(known) = assumptions.known_signed_constant_after_normalization(value)
            {
                constant += known * byte_width;
                continue;
            }
            unresolved.push(atom);
        }
        (unresolved, constant)
    };
    let (left_atoms, left_constant) = resolve(left);
    let (mut right_atoms, right_constant) = resolve(right);
    if left_constant != right_constant {
        return false;
    }
    // Scaled values compare through snapshot-bridged load equality: two
    // spellings of one loaded field, or a recorded PointerOffsetEqual fact
    // whose sides bridge to the compared values.
    let scaled_values_bridged = |left: &Bitvector32Term, right: &Bitvector32Term| {
        left == right
            || bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
            || assumptions.memory_loads_proven_equal(left, right)
            || matches!((left, right), (
                Bitvector32Term::MemoryLoad(left_memory, left_pointer),
                Bitvector32Term::MemoryLoad(right_memory, right_pointer),
            ) if left_pointer == right_pointer
                && (crate::kernel::c_memory_load_is_unchanged(
                    left_memory,
                    right_memory,
                    left_pointer,
                    assumptions,
                ) || crate::kernel::c_memory_load_is_unchanged(
                    right_memory,
                    left_memory,
                    right_pointer,
                    assumptions,
                )))
    };
    let atoms_match = |left: &PointerOffsetTerm, right: &PointerOffsetTerm| {
        if left == right
            || assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
                left.clone(),
                right.clone(),
            )) == Some(true)
            || assumptions.exact_condition_value(&ConditionTerm::pointer_offset_equal(
                right.clone(),
                left.clone(),
            )) == Some(true)
        {
            return true;
        }
        let (
            PointerOffsetTerm::Int32Scaled {
                value: left_value,
                byte_width: left_width,
            },
            PointerOffsetTerm::Int32Scaled {
                value: right_value,
                byte_width: right_width,
            },
        ) = (left, right)
        else {
            return false;
        };
        if left_width != right_width {
            return false;
        }
        if scaled_values_bridged(left_value, right_value) {
            return true;
        }
        // Walk the PointerOffsetEqual fact graph transitively: each edge's
        // endpoints connect to the frontier through snapshot-bridged load
        // equality, so a chain like right->data == left->data == data closes.
        let edges = assumptions
            .condition_facts
            .iter()
            .filter(|(_, value)| **value)
            .filter_map(|(condition, _)| {
                let ConditionTerm::PointerOffsetEqual(fact_left, fact_right) = condition else {
                    return None;
                };
                let (
                    PointerOffsetTerm::Int32Scaled {
                        value: a_value,
                        byte_width: a_width,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: b_value,
                        byte_width: b_width,
                    },
                ) = (fact_left.as_ref(), fact_right.as_ref())
                else {
                    return None;
                };
                (a_width == left_width && b_width == left_width)
                    .then_some((a_value.as_ref().clone(), b_value.as_ref().clone()))
            })
            .collect::<Vec<_>>();
        let mut frontier = vec![left_value.as_ref().clone()];
        let mut visited = Vec::new();
        while let Some(current) = frontier.pop() {
            if visited.contains(&current) {
                continue;
            }
            if scaled_values_bridged(&current, right_value) {
                return true;
            }
            for (a_value, b_value) in &edges {
                if scaled_values_bridged(&current, a_value) {
                    frontier.push(b_value.clone());
                }
                if scaled_values_bridged(&current, b_value) {
                    frontier.push(a_value.clone());
                }
            }
            visited.push(current);
        }
        false
    };
    for atom in &left_atoms {
        let Some(position) = right_atoms
            .iter()
            .position(|candidate| atoms_match(atom, candidate))
        else {
            return false;
        };
        right_atoms.remove(position);
    }
    right_atoms.is_empty()
}

/// The load spellings a term denotes: the term itself when it is a load,
/// plus every load one equality fact away.
fn load_spellings_of<'a>(
    assumptions: &'a Assumptions,
    term: &'a Bitvector32Term,
) -> Vec<(&'a CMemory, &'a Pointer)> {
    let mut loads = Vec::new();
    if let Bitvector32Term::MemoryLoad(memory, pointer) = term {
        loads.push((&**memory, pointer.as_ref()));
    }
    for (condition, value) in assumptions.condition_facts.iter() {
        if !*value {
            continue;
        }
        let ConditionTerm::Bitvector32Equal(fact_left, fact_right) = condition else {
            continue;
        };
        for (fact_term, fact_load) in [(fact_left, fact_right), (fact_right, fact_left)] {
            if fact_term.as_ref() != term {
                continue;
            }
            if let Bitvector32Term::MemoryLoad(memory, pointer) = fact_load.as_ref() {
                loads.push((&**memory, pointer.as_ref()));
            }
        }
    }
    loads
}

/// Certifies an equality by resolving each side to a load spelling (itself,
/// or one equality fact away) and proving some pair of spellings denotes one
/// framed cell: same block, offsets equal with constant-resolved atoms, and
/// the loaded cell provably unchanged between the two snapshots.
fn certification_proves_equality_via_load_fact(
    assumptions: &Assumptions,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> bool {
    let left_loads = load_spellings_of(assumptions, left);
    if left_loads.is_empty() {
        return false;
    }
    let right_loads = load_spellings_of(assumptions, right);
    left_loads.iter().any(|(left_memory, left_pointer)| {
        right_loads.iter().any(|(right_memory, right_pointer)| {
            left_pointer.block == right_pointer.block
                && pointer_offsets_equal_with_resolved_atoms(
                    &left_pointer.offset,
                    &right_pointer.offset,
                    assumptions,
                )
                && [left_pointer, right_pointer].into_iter().any(|pointer| {
                    c_memory_load_is_unchanged(left_memory, right_memory, pointer, assumptions)
                        || c_memory_load_is_unchanged(
                            right_memory,
                            left_memory,
                            pointer,
                            assumptions,
                        )
                })
        })
    })
}

pub(super) fn certification_proves_proposition(
    assumptions: &Assumptions,
    proposition: &Proposition,
) -> bool {
    if assumptions.proves_exact(proposition) {
        return true;
    }
    if matches!(proposition, Proposition::ForAll { .. })
        && assumptions
            .prop_facts
            .iter()
            .any(|fact| propositions_alpha_equivalent(fact, proposition))
    {
        // Bound variables are freshened independently while the contract
        // assumptions and proof-derived entry facts are lowered. The
        // proposition is already assumed modulo that irrelevant binder
        // spelling, so do not route hundreds of such facts through general
        // quantified proof search.
        return true;
    }
    if let Proposition::ConditionIs(condition, value) = proposition
        && let Some(canonical) = condition_with_canonical_loads(condition)
        && &canonical != condition
        && certification_proves_proposition(
            assumptions,
            &Proposition::ConditionIs(canonical, *value),
        )
    {
        return true;
    }
    if let Proposition::ConditionIs(condition, value) = proposition
        && assumptions.prop_facts.iter().any(|fact| {
            assumptions
                .forall_instantiations_for_condition(fact, condition)
                .into_iter()
                .any(|instance| {
                    let mut body = &instance;
                    let mut premises = Vec::new();
                    while let Proposition::Implies(premise, rest) = body {
                        premises.push(premise.as_ref());
                        body = rest;
                    }
                    let Proposition::ConditionIs(_, instance_value) = body else {
                        return false;
                    };
                    instance_value == value
                        && c_condition_facts_equivalent_for_memory_resolution(
                            body,
                            &Proposition::ConditionIs(condition.clone(), *value),
                            assumptions,
                        )
                        && premises
                            .into_iter()
                            .all(|premise| certification_proves_proposition(assumptions, premise))
                })
        })
    {
        return true;
    }
    match proposition {
        // Order conditions use the deterministic bounded order prover; the
        // fuel-dependent simp decision procedure stays out of certification.
        Proposition::ConditionIs(condition, value)
            if assumptions.proves_order_condition_for_memory_resolution(condition, *value) =>
        {
            true
        }
        Proposition::ConditionIs(condition, value)
            if shifted_order_condition_proven(assumptions, condition, *value) =>
        {
            true
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if range_folds_alpha_equivalent(left, right) =>
        {
            true
        }
        // Both sides resolve to one known constant through equality facts
        // and per-load snapshot bridging (deterministic and fuel-free).
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && assumptions.constants_known_equal_after_normalization(left, right) =>
        {
            true
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && assumptions
                    .exact_signed_intervals_equal(left, right)
                    .is_some_and(|equal| equal) =>
        {
            true
        }
        // A signed comparison whose sides both resolve to known constants
        // through equality facts and per-load snapshot bridging.
        Proposition::ConditionIs(condition, value)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && assumptions
                    .signed_comparison_by_constant_normalization(condition)
                    .is_some_and(|known| known == *value) =>
        {
            true
        }
        // One side equals a recorded load spelling by an equality fact and
        // the two loads denote the same framed cell.
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true)
            if std::env::var_os("CLICK_DISABLE_CERT_ARMS").is_none()
                && certification_proves_equality_via_load_fact(assumptions, left, right) =>
        {
            true
        }
        Proposition::And(left, right) => {
            certification_proves_proposition(assumptions, left)
                && certification_proves_proposition(assumptions, right)
        }
        Proposition::Or(left, right) => {
            certification_proves_proposition(assumptions, left)
                || certification_proves_proposition(assumptions, right)
                // Excluded middle over decidable conditions: `L or R` holds
                // when assuming `not L` certifies `R` (and symmetrically).
                || match left.as_ref() {
                    Proposition::ConditionIs(condition, value) => {
                        let negated = assumptions.clone().assume_proposition(
                            Proposition::ConditionIs(condition.clone(), !value),
                        );
                        certification_proves_proposition(&negated, right)
                    }
                    _ => false,
                }
                || match right.as_ref() {
                    Proposition::ConditionIs(condition, value) => {
                        let negated = assumptions.clone().assume_proposition(
                            Proposition::ConditionIs(condition.clone(), !value),
                        );
                        certification_proves_proposition(&negated, left)
                    }
                    _ => false,
                }
        }
        Proposition::Exists {
            var,
            sort: sort @ (Sort::CInt32 | Sort::Bitvector32),
            body,
            ..
        } => {
            // An assumed existential proves the goal up to renaming of the
            // bound variable; bound variables are freshened per lowering
            // pass, so exact matching alone would never fire.
            let alpha_matched = assumptions.prop_facts.iter().any(|fact| {
                let Proposition::Exists {
                    var: fact_var,
                    sort: fact_sort,
                    body: fact_body,
                    ..
                } = fact
                else {
                    return false;
                };
                if fact_sort != sort {
                    return false;
                }
                let renamed = substitute_bitvector_variable_in_proposition(
                    fact_body,
                    *fact_var,
                    &Bitvector32Term::Variable(*var),
                );
                if propositions_alpha_equivalent(&renamed, body) {
                    return true;
                }
                // Weakening under the binder: an existential of a
                // conjunction proves the existential of any subset of its
                // conjuncts.
                let mut fact_conjuncts = Vec::new();
                proposition_conjuncts(&renamed, &mut fact_conjuncts);
                let mut goal_conjuncts = Vec::new();
                proposition_conjuncts(body, &mut goal_conjuncts);
                goal_conjuncts.iter().all(|goal| {
                    fact_conjuncts
                        .iter()
                        .any(|fact| propositions_alpha_equivalent(fact, goal))
                })
            });
            if alpha_matched {
                return true;
            }
            // One-point rule: `P[t/x]` proves `exists x. P` when a conjunct
            // pins `x` to a witness term `t`.
            let mut candidates = Vec::new();
            exists_equality_witness_candidates(*var, body, &mut candidates);
            candidates.into_iter().any(|witness| {
                let instantiated =
                    substitute_bitvector_variable_in_proposition(body, *var, &witness);
                certification_proves_proposition(assumptions, &instantiated)
            })
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
                || assumptions
                    .has_anchored_bitvector_equality_fact_for_memory_resolution(left, right)
                || assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(
                        left.as_ref().clone(),
                        right.as_ref().clone(),
                    ),
                    true,
                ) && assumptions.proves_order_condition_for_memory_resolution(
                    &ConditionTerm::signed_less_equal(
                        right.as_ref().clone(),
                        left.as_ref().clone(),
                    ),
                    true,
                )
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
            pointers_proven_equal_for_memory_resolution(left, right, assumptions)
                || assumptions.has_pointer_equality_path(left, right)
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            pointer_offsets_proven_equal_for_memory_resolution(left, right, assumptions)
                || pointer_offsets_equal_with_resolved_atoms(left, right, assumptions)
        }
        Proposition::Equal(Term::CValue(left), Term::CValue(right)) => {
            c_values_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves_order_condition_for_memory_resolution(condition, *value)
                || assumptions.has_matching_condition_fact_for_memory_resolution(condition, *value)
        }
        Proposition::Predicate { .. } => {
            assumptions.proves(proposition)
                || certification_proves_predicate_from_quantified_implication(
                    assumptions,
                    proposition,
                )
        }
        _ => assumptions.proves(proposition),
    }
}

/// Reuses a closed quantified fact only after the kernel has proved it from
/// previously proved closed quantified facts. Contract certification sees
/// the same ordered global theorem facts once per function; this cache keeps
/// their proof independent of every function entry state. Failures are never
/// cached because a bounded proof attempt may have observed the active
/// deadline.
pub(in crate::kernel) fn certification_proves_context_free_forall(
    proposition: &Proposition,
) -> bool {
    if !matches!(proposition, Proposition::ForAll { .. }) {
        return false;
    }
    thread_local! {
        static PROVED: std::cell::RefCell<BTreeSet<Proposition>> =
            const { std::cell::RefCell::new(BTreeSet::new()) };
    }
    if PROVED.with(|proved| proved.borrow().contains(proposition)) {
        return true;
    }
    let proved_facts = PROVED.with(|proved| proved.borrow().iter().cloned().collect::<Vec<_>>());
    let closed_assumptions = assumptions_with_propositions(&Assumptions::new(), &proved_facts);
    let proved = certification_proves_proposition(&closed_assumptions, proposition);
    if proved && crate::instrumentation::exceeded_verification_limit_context().is_none() {
        PROVED.with(|cache| {
            let mut cache = cache.borrow_mut();
            if cache.len() >= 128 {
                cache.pop_first();
            }
            cache.insert(proposition.clone());
        });
    }
    proved
}

/// True for a closed universally-quantified implication chain that concludes
/// in an opaque predicate — the shape of a surface-verified theorem fact.
fn quantified_predicate_implication_fact(fact: &Proposition) -> bool {
    let mut body = fact;
    let mut binders = 0usize;
    while let Proposition::ForAll { body: inner, .. } = body {
        binders += 1;
        body = inner.as_ref();
    }
    if binders == 0 {
        return false;
    }
    while let Proposition::Implies(_, rest) = body {
        body = rest.as_ref();
    }
    matches!(body, Proposition::Predicate { .. })
}

/// Certifies an opaque predicate goal by instantiating an assumed
/// universally-quantified implication (typically a verified theorem): the
/// fact's predicate conclusion pins each bound variable against the goal's
/// arguments, and every premise must then certify under that instantiation.
fn certification_proves_predicate_from_quantified_implication(
    assumptions: &Assumptions,
    goal: &Proposition,
) -> bool {
    let Proposition::Predicate { name, arguments } = goal else {
        return false;
    };
    assumptions.prop_facts.iter().any(|fact| {
        let mut binders = Vec::new();
        let mut body = fact;
        while let Proposition::ForAll {
            var, body: inner, ..
        } = body
        {
            binders.push(*var);
            body = inner.as_ref();
        }
        if binders.is_empty() {
            return false;
        }
        let mut premises = Vec::new();
        let mut conclusion = body;
        while let Proposition::Implies(premise, rest) = conclusion {
            premises.push(premise.as_ref().clone());
            conclusion = rest.as_ref();
        }
        let Proposition::Predicate {
            name: fact_name,
            arguments: fact_arguments,
        } = conclusion
        else {
            return false;
        };
        if fact_name != name || fact_arguments.len() != arguments.len() {
            return false;
        }
        let mut substitution: Vec<(Variable, Bitvector32Term)> = Vec::new();
        for (fact_argument, goal_argument) in fact_arguments.iter().zip(arguments) {
            let bound_variable = match fact_argument {
                Term::CValue(
                    CValue::Int32(Bitvector32Term::Variable(var))
                    | CValue::UInt8(Bitvector32Term::Variable(var)),
                ) if binders.contains(var) => Some(*var),
                _ => None,
            };
            let Some(var) = bound_variable else {
                if fact_argument != goal_argument {
                    return false;
                }
                continue;
            };
            let goal_term = match goal_argument {
                Term::CValue(CValue::Int32(term) | CValue::UInt8(term)) => term.clone(),
                Term::Bitvector32(term) => term.clone(),
                _ => return false,
            };
            match substitution.iter().find(|(existing, _)| *existing == var) {
                None => substitution.push((var, goal_term)),
                Some((_, existing)) if *existing == goal_term => {}
                Some(_) => return false,
            }
        }
        if binders
            .iter()
            .any(|var| !substitution.iter().any(|(bound, _)| bound == var))
        {
            return false;
        }
        premises.into_iter().all(|premise| {
            let mut instantiated = premise;
            for (var, witness) in &substitution {
                instantiated =
                    substitute_bitvector_variable_in_proposition(&instantiated, *var, witness);
            }
            certification_proves_proposition(assumptions, &instantiated)
        })
    })
}

fn certification_proves_post_proposition(
    assumptions: &Assumptions,
    proposition: &Proposition,
    post_memory: &CMemory,
    execution_facts: &[ExecutionPureFact],
) -> bool {
    if certification_proves_proposition(assumptions, proposition) {
        return true;
    }
    // Verified calls contribute independently certified public
    // postconditions. Keep their explicit snapshots and reason from the
    // complete set: a later call may relate the final state to an earlier
    // snapshot while another postcondition relates that snapshot to a local
    // result. Checking one call fact at a time loses exactly that valid
    // composition.
    let public_condition_facts = execution_facts
        .iter()
        .filter(|fact| fact.is_public() && fact.is_certified())
        .filter_map(|fact| match fact.proposition() {
            proposition @ Proposition::ConditionIs(_, _) => Some(proposition.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    if !public_condition_facts.is_empty()
        && certification_proves_proposition(
            &assumptions_with_propositions(assumptions, &public_condition_facts),
            proposition,
        )
    {
        return true;
    }
    if execution_facts
        .iter()
        .enumerate()
        .filter(|(_, fact)| fact.is_certified())
        .any(|(source_index, fact)| {
            let Some(CertifiedMemoryStore {
                after,
                pointer,
                value: CValue::Int32(value) | CValue::UInt8(value),
                authorized_range,
                ..
            }) = fact.certified_store_data()
            else {
                return false;
            };
            let mut current = after;
            for later in &execution_facts[source_index + 1..] {
                let Some(CertifiedMemoryStore {
                    before,
                    after,
                    pointer: later_pointer,
                    authorized_range: later_range,
                    ..
                }) = later.certified_store_data()
                else {
                    continue;
                };
                if before != current {
                    continue;
                }
                let disjoint = pointer.blocks_proven_distinct(later_pointer)
                    || pointers_proven_distinct_for_memory_resolution(
                        pointer,
                        later_pointer,
                        assumptions,
                    )
                    || authorized_range.as_ref().is_some_and(|source_range| {
                        later_range.as_ref().is_some_and(|later_range| {
                            assumptions
                                .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                                    source_range,
                                    later_range,
                                )
                        })
                    });
                if !disjoint {
                    return false;
                }
                current = after;
            }
            if current != post_memory
                && !c_memory_load_is_unchanged(current, post_memory, pointer, assumptions)
            {
                return false;
            }
            let stored_fact = Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(post_memory.clone()),
                        Box::new(pointer.clone()),
                    ),
                    value.clone(),
                ),
                true,
            );
            let stored_assumptions =
                assumptions_with_propositions(assumptions, &[stored_fact]);
            certification_proves_proposition(&stored_assumptions, proposition)
        })
    {
        return true;
    }
    let transported_fact_proves = |fact: &Proposition| {
        let Some(theorem) = prove_c_condition_fact_transport(fact, post_memory, assumptions) else {
            return false;
        };
        let Proposition::Implies(source, target) = theorem.proposition() else {
            return false;
        };
        if source.as_ref() != fact {
            return false;
        }
        let transported_assumptions =
            assumptions_with_propositions(assumptions, &[target.as_ref().clone()]);
        certification_proves_proposition(&transported_assumptions, proposition)
    };
    let explicit_facts = execution_facts
        .iter()
        .filter(|fact| fact.is_certified())
        .filter_map(|fact| match fact.proposition() {
            proposition @ Proposition::ConditionIs(_, _) => Some(proposition.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    explicit_facts
        .iter()
        .filter(|fact| {
            matches!(
                (*fact, proposition),
                (
                    Proposition::ConditionIs(_, _),
                    Proposition::ConditionIs(_, _)
                ) | (Proposition::Equal(_, _), Proposition::Equal(_, _))
            )
        })
        .any(transported_fact_proves)
}

pub(super) fn resources_certify_loadability(
    state: &CState,
    resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> bool {
    match proposition {
        Proposition::ForAll { body, .. } => {
            return resources_certify_loadability(state, resources, body, assumptions);
        }
        Proposition::Implies(premise, conclusion) => {
            let assumptions = assumptions
                .clone()
                .assume_proposition(premise.as_ref().clone());
            return resources_certify_loadability(state, resources, conclusion, &assumptions);
        }
        Proposition::And(left, right) => {
            return resources_certify_loadability(state, resources, left, assumptions)
                && resources_certify_loadability(state, resources, right, assumptions);
        }
        _ => {}
    }
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
    } = proposition
    else {
        return false;
    };
    memory_snapshots_proven_equal_at_pointer(memory, state.memory(), base, assumptions)
        && bytes
            .as_const()
            .is_some_and(|bytes| resource_context_has_read(resources, base, bytes, assumptions))
}

fn contract_endpoints_certify_loadability(
    entry_state: &CState,
    entry_resources: &ResourceContext,
    post_state: &CState,
    post_resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> bool {
    resources_certify_loadability(entry_state, entry_resources, proposition, assumptions)
        || resources_certify_loadability(post_state, post_resources, proposition, assumptions)
}
