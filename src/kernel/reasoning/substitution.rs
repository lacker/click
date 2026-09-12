use super::*;
use num_traits::ToPrimitive;

/// Rewrites kernel-minted load variables back to their defining load terms,
/// using the certified defining equations the canonicalizing loader pushed
/// into the execution fact stream. Surface synthesis calls this before
/// form a kernel fact, so a fact mentioning a minted variable writes as
/// the loaded expression the source actually wrote.
/// The pointer-level companion of [`resolve_minted_load_variables`]: rewrites
/// kernel-minted load variables inside a pointer's offset using
/// defining-shaped equations drawn from an assumption context. Range and
/// containment provers call this on their query pointer so a minted address
/// matches ranges still written through loads.
pub(crate) fn resolve_minted_load_pointer(
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Pointer {
    let mut resolved = pointer.clone();
    let mut defining = 0usize;
    for fact in assumptions.prop_facts.iter() {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = fact
        else {
            continue;
        };
        let (Bitvector32Term::Variable(variable), load @ Bitvector32Term::MemoryLoad(_, _)) =
            (left.as_ref(), right.as_ref())
        else {
            continue;
        };
        defining += 1;
        resolved.offset =
            substitute_bitvector_variable_in_pointer_offset(&resolved.offset, *variable, load);
    }
    let _ = defining;
    resolved
}

#[cfg(test)]
mod resource_frame_substitution_tests {
    use super::*;

    fn inherited_check(range: CMemoryRange) -> CLoopEffectCheck {
        CLoopEffectCheck {
            effect: CLoopEffect::Mutable(Vec::new()),
            span: CLoopEffectSpan::Whole,
            context: None,
            origin: CLoopEffectOrigin::InheritedResourceDerived,
            validated_ranges: Some(vec![range]),
        }
    }

    #[test]
    fn bitvector_substitution_rewrites_validated_inherited_ranges() {
        let from = Variable(71_001);
        let range = CMemoryRange::new(
            Pointer {
                block: PointerBlock::Concrete("substitution:range".into()),
                offset: PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(from)),
                    byte_width: 4,
                },
            },
            Bitvector32Term::Variable(from),
            Bitvector32Term::Add(
                Box::new(Bitvector32Term::Variable(from)),
                Box::new(Bitvector32Term::Constant(1)),
            ),
        );
        let statement = CStatement::While {
            condition: c_int32_literal(0),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: vec![inherited_check(range)],
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            body: Box::new(CStatement::Skip),
            do_while: false,
        };
        let substituted = substitute_bitvector_variable_in_c_statement(
            &statement,
            from,
            &Bitvector32Term::Constant(4),
        );
        let CStatement::While { effect_checks, .. } = substituted else {
            panic!("substitution changed the statement shape");
        };
        let actual = effect_checks[0]
            .validated_ranges()
            .expect("validated carrier must be retained");
        assert_eq!(actual[0].start, Bitvector32Term::Constant(4));
        assert_eq!(actual[0].end, Bitvector32Term::Constant(5));
        assert_eq!(actual[0].base.offset, PointerOffsetTerm::Constant(16));
    }

    #[test]
    fn pointer_substitution_rewrites_validated_ranges_and_derived_interface() {
        let from = Variable(71_002);
        let replacement = Pointer {
            block: PointerBlock::Concrete("substitution:replacement".into()),
            offset: PointerOffsetTerm::Constant(2),
        };
        let range = CMemoryRange::new(
            Pointer {
                block: PointerBlock::Symbolic(from),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        );
        let statement = CStatement::While {
            condition: c_int32_literal(0),
            invariant: Vec::new(),
            invariant_checks: Vec::new(),
            effect_checks: vec![inherited_check(range)],
            resource_specs: Vec::new(),
            ranking_measures: Vec::new(),
            structural_measure: None,
            body: Box::new(CStatement::Skip),
            do_while: false,
        };
        let substituted =
            substitute_pointer_variable_in_c_statement(&statement, from, &replacement);
        let CStatement::While { effect_checks, .. } = substituted else {
            panic!("substitution changed the statement shape");
        };
        assert_eq!(
            effect_checks[0].validated_ranges().unwrap()[0].base.offset,
            replacement.offset
        );

        let derived_segment = CMemorySegment::new(
            CExpression::Value(CValue::pointer(Pointer {
                block: PointerBlock::Symbolic(from),
                offset: PointerOffsetTerm::Constant(0),
            })),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(1)),
        );
        let function = CFunction::new(CType::Void, "substitution", Vec::new(), statement)
            .with_resource_summary(Vec::new(), Vec::new())
            .with_resource_derived_mutable_segments(vec![derived_segment])
            .with_resource_derived_mutable_frame();
        let substituted = substitute_pointer_variable_in_c_function(&function, from, &replacement);
        assert!(substituted.resource_derived_mutable_frame());
        assert_eq!(
            substituted
                .contract_interface()
                .resource_derived_mutable_segments[0]
                .base,
            CExpression::Value(CValue::pointer(replacement))
        );
    }
}

/// Rewrites a havoced symbolic pointer local through one explicit pointer
/// equality. The equality is deliberately limited to an exact fact and one
/// hop: resource lookup can use the concrete block's index without turning
/// alias reasoning into an unbounded graph walk.
pub(crate) fn resolve_symbolic_pointer_alias(
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> Pointer {
    if !matches!(pointer.block, PointerBlock::Symbolic(_)) {
        return pointer.clone();
    }
    assumptions
        .condition_facts
        .iter()
        .find_map(|(condition, value)| {
            if !*value {
                return None;
            }
            let ConditionTerm::PointerEqual(left, right) = condition else {
                return None;
            };
            if left.as_ref() == pointer && !matches!(right.block, PointerBlock::Symbolic(_)) {
                Some(right.as_ref().clone())
            } else if right.as_ref() == pointer && !matches!(left.block, PointerBlock::Symbolic(_))
            {
                Some(left.as_ref().clone())
            } else {
                None
            }
        })
        .unwrap_or_else(|| pointer.clone())
}

/// Resolves load variables in a proposition through
/// defining-equation propositions (`v == load(snapshot, ptr)`), restoring
/// the load terms. For surface-form synthesis, where the internal
/// names have no surface form but their loads do.
/// Resolves load variables in a proposition through the
/// thread-local registry, restoring the load terms the internal names
/// stand for. For surface-form synthesis when no defining equation is
/// in scope: the registry is the mint's own record of what each canonical
/// variable names.
pub fn resolve_load_variables_from_registry(proposition: &Proposition) -> Proposition {
    let mut variables = std::collections::BTreeSet::new();
    super::variable_collection::collect_proposition_bitvector_variables(
        proposition,
        &mut variables,
    );
    let mut resolved = proposition.clone();
    for variable in variables {
        if !crate::kernel::eval::is_load_variable(&variable) {
            continue;
        }
        let Some((memory, pointer)) =
            crate::kernel::eval::registered_load_origin_for_variable(&variable)
        else {
            continue;
        };
        let load = Bitvector32Term::MemoryLoad(memory, Box::new(pointer));
        resolved = substitute_bitvector_variable_in_proposition(&resolved, variable, &load);
    }
    resolved
}

pub fn resolve_load_variables_via(
    proposition: &Proposition,
    defining: &[Proposition],
) -> Proposition {
    let mut resolved = proposition.clone();
    for fact in defining {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) = fact
        else {
            continue;
        };
        let (Bitvector32Term::Variable(variable), load @ Bitvector32Term::MemoryLoad(_, _)) =
            (left.as_ref(), right.as_ref())
        else {
            continue;
        };
        if !crate::kernel::eval::is_load_variable(variable) {
            continue;
        }
        resolved = substitute_bitvector_variable_in_proposition(&resolved, *variable, load);
    }
    resolved
}

pub fn resolve_minted_load_variables(
    proposition: &Proposition,
    facts: &[ExecutionPureFact],
) -> Proposition {
    let mut resolved = proposition.clone();
    for fact in facts {
        if !fact.certified {
            continue;
        }
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            &fact.proposition
        else {
            continue;
        };
        let (Bitvector32Term::Variable(variable), load @ Bitvector32Term::MemoryLoad(_, _)) =
            (left.as_ref(), right.as_ref())
        else {
            continue;
        };
        resolved = substitute_bitvector_variable_in_proposition(&resolved, *variable, load);
    }
    resolved
}

pub(crate) fn substitute_bitvector_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &Bitvector32Term,
) -> Proposition {
    match proposition {
        Proposition::Equal(left, right) => Proposition::Equal(
            substitute_bitvector_variable_in_term(left, from, to),
            substitute_bitvector_variable_in_term(right, from, to),
        ),
        Proposition::ConditionIs(condition, value) => Proposition::ConditionIs(
            substitute_bitvector_variable_in_condition(condition, from, to),
            *value,
        ),
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_term(argument, from, to))
                .collect(),
        },
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::CExpressionEvaluates {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            expression: substitute_bitvector_variable_in_c_expression(expression, from, to),
            outcome: substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        } => Proposition::CStatementExecutes {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            statement: substitute_bitvector_variable_in_c_statement(statement, from, to),
            outcome: substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        },
        Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => Proposition::CStatementVerifies {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            statement: substitute_bitvector_variable_in_c_statement(statement, from, to),
            outcome: substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        },
        Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome,
        } => Proposition::CFunctionExecutes {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            outcome: substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        },
        Proposition::CFunctionVerifies {
            state,
            function,
            arguments,
            outcome,
        } => Proposition::CFunctionVerifies {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            outcome: substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        },
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionSatisfiesSpecification {
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            specification: substitute_bitvector_variable_in_c_function_specification(
                specification,
                from,
                to,
            ),
        },
        Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionPartiallySatisfiesSpecification {
            function: substitute_bitvector_variable_in_c_function(function, from, to),
            specification: substitute_bitvector_variable_in_c_function_specification(
                specification,
                from,
                to,
            ),
        },
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => Proposition::CMemoryLoads {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_pointer(pointer, from, to),
            outcome: substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => Proposition::CMemoryCanStore {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_pointer(pointer, from, to),
            byte_width: *byte_width,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryLoadable {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            base: substitute_bitvector_variable_in_pointer(base, from, to),
            bytes: substitute_bitvector_variable(bytes, from, to),
        },
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => Proposition::CMemoryDisjoint {
            left_base: substitute_bitvector_variable_in_pointer(left_base, from, to),
            left_start: substitute_bitvector_variable(left_start, from, to),
            left_end: substitute_bitvector_variable(left_end, from, to),
            right_base: substitute_bitvector_variable_in_pointer(right_base, from, to),
            right_start: substitute_bitvector_variable(right_start, from, to),
            right_end: substitute_bitvector_variable(right_end, from, to),
        },
        Proposition::CResourceSeparate { left, right } => Proposition::CResourceSeparate {
            left: substitute_bitvector_variable_in_c_resource(left, from, to),
            right: substitute_bitvector_variable_in_c_resource(right, from, to),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: substitute_bitvector_variable_in_c_resource(parent, from, to),
            child: substitute_bitvector_variable_in_c_resource(child, from, to),
        },
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => Proposition::CMemoryMutatesOnly {
            before: substitute_bitvector_variable_in_memory(before, from, to),
            after: substitute_bitvector_variable_in_memory(after, from, to),
            pointers: pointers
                .iter()
                .map(|pointer| substitute_bitvector_variable_in_pointer(pointer, from, to))
                .collect(),
        },
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => Proposition::CMemoryEffectSummary {
            before: substitute_bitvector_variable_in_memory(before, from, to),
            after: substitute_bitvector_variable_in_memory(after, from, to),
            mutable_ranges: mutable_ranges
                .iter()
                .map(|range| substitute_bitvector_variable_in_c_memory_range(range, from, to))
                .collect(),
        },
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => Proposition::CHeapAllocationFreed {
            before: substitute_bitvector_variable_in_memory(before, from, to),
            after: substitute_bitvector_variable_in_memory(after, from, to),
            allocation_base: substitute_bitvector_variable_in_pointer(allocation_base, from, to),
            bytes: substitute_bitvector_variable(bytes, from, to),
        },
        Proposition::And(left, right) => Proposition::And(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(
            substitute_bitvector_variable_in_proposition(body, from, to),
        )),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(substitute_bitvector_variable_in_proposition(left, from, to)),
            Box::new(substitute_bitvector_variable_in_proposition(
                right, from, to,
            )),
        ),
        Proposition::ForAll { var, sort, body } if *var != from => {
            let (var, body) = capture_avoiding_quantifier_body(*var, body, from, to);
            Proposition::ForAll {
                var,
                sort: sort.clone(),
                body: Box::new(substitute_bitvector_variable_in_proposition(
                    &body, from, to,
                )),
            }
        }
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } if *var != from => {
            let (var, body) = capture_avoiding_quantifier_body(*var, body, from, to);
            Proposition::Exists {
                name: name.clone(),
                var,
                sort: sort.clone(),
                body: Box::new(substitute_bitvector_variable_in_proposition(
                    &body, from, to,
                )),
            }
        }
        proposition => proposition.clone(),
    }
}

/// Applies a finite substitution to free variables simultaneously.
///
/// Sequentially applying a map is unsound when one replacement mentions a
/// variable that is also a key in the map: the later replacement rewrites the
/// value just installed by the earlier one.  Stage every source through a
/// fresh variable first, then install the requested replacements in a second
/// pass.  The ordinary substitution routine handles capture avoidance at each
/// quantifier boundary.
pub(in crate::kernel) fn substitute_bitvector_variables_in_proposition(
    proposition: &Proposition,
    substitutions: &BTreeMap<Variable, Bitvector32Term>,
) -> Proposition {
    if substitutions.is_empty() {
        return proposition.clone();
    }

    let mut reserved = BTreeSet::new();
    collect_proposition_bitvector_variables(proposition, &mut reserved);
    collect_proposition_bound_variables(proposition, &mut reserved);
    for (source, replacement) in substitutions {
        reserved.insert(*source);
        collect_bitvector_variables(replacement, &mut reserved);
    }

    let mut fresh_variables = KernelVariableGenerator::fresh_for(0, reserved);
    let staged = substitutions
        .keys()
        .map(|source| (*source, fresh_variables.next()))
        .collect::<Vec<_>>();

    let mut result = proposition.clone();
    for (source, temporary) in &staged {
        result = substitute_bitvector_variable_in_proposition(
            &result,
            *source,
            &Bitvector32Term::Variable(*temporary),
        );
    }
    for (source, temporary) in staged {
        result = substitute_bitvector_variable_in_proposition(
            &result,
            temporary,
            &substitutions[&source],
        );
    }
    result
}

fn capture_avoiding_quantifier_body(
    binder: Variable,
    body: &Proposition,
    substituted: Variable,
    replacement: &Bitvector32Term,
) -> (Variable, Proposition) {
    let mut replacement_variables = BTreeSet::new();
    collect_bitvector_variables(replacement, &mut replacement_variables);
    if !replacement_variables.contains(&binder) {
        return (binder, body.clone());
    }

    let mut reserved = replacement_variables;
    collect_proposition_bitvector_variables(body, &mut reserved);
    collect_proposition_bound_variables(body, &mut reserved);
    reserved.insert(binder);
    reserved.insert(substituted);
    let mut variables = KernelVariableGenerator::fresh_for(0, reserved);
    let fresh = variables.next();
    let renamed = substitute_bitvector_variable_in_proposition(
        body,
        binder,
        &Bitvector32Term::Variable(fresh),
    );
    (fresh, renamed)
}

pub(in crate::kernel) fn collect_proposition_bound_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        Proposition::Equal(left, right) => {
            collect_term_bound_variables(left, variables);
            collect_term_bound_variables(right, variables);
        }
        Proposition::ConditionIs(condition, _) => {
            collect_condition_bound_variables(condition, variables);
        }
        Proposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_term_bound_variables(argument, variables);
            }
        }
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_expression_bound_variables(expression, variables);
            collect_expression_outcome_bound_variables(outcome, variables);
        }
        Proposition::CConditionEvaluates {
            state, condition, ..
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_expression_bound_variables(condition, variables);
        }
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        }
        | Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_statement_bound_variables(statement, variables);
            collect_statement_outcome_bound_variables(outcome, variables);
        }
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
        } => {
            collect_c_state_bound_variables(state, variables);
            collect_c_function_bound_variables(function, variables);
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
            collect_function_outcome_bound_variables(outcome, variables);
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        }
        | Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => {
            collect_c_function_bound_variables(function, variables);
            collect_c_function_specification_bound_variables(specification, variables);
        }
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(pointer, variables);
            collect_expression_outcome_bound_variables(outcome, variables);
        }
        Proposition::CMemoryCanStore {
            memory, pointer, ..
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(pointer, variables);
        }
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => {
            collect_memory_bound_variables(memory, variables);
            collect_pointer_bound_variables(base, variables);
            collect_bitvector_bound_variables(bytes, variables);
        }
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => {
            collect_pointer_bound_variables(left_base, variables);
            collect_bitvector_bound_variables(left_start, variables);
            collect_bitvector_bound_variables(left_end, variables);
            collect_pointer_bound_variables(right_base, variables);
            collect_bitvector_bound_variables(right_start, variables);
            collect_bitvector_bound_variables(right_end, variables);
        }
        Proposition::CResourceSeparate { left, right }
        | Proposition::CResourceContains {
            parent: left,
            child: right,
        } => {
            collect_resource_bound_variables(left, variables);
            collect_resource_bound_variables(right, variables);
        }
        Proposition::CResourceComposition(resources) => {
            for fact in resources.facts() {
                collect_resource_bound_variables(fact.resource(), variables);
            }
        }
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => {
            collect_memory_bound_variables(before, variables);
            collect_memory_bound_variables(after, variables);
            for pointer in pointers {
                collect_pointer_bound_variables(pointer, variables);
            }
        }
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => {
            collect_memory_bound_variables(before, variables);
            collect_memory_bound_variables(after, variables);
            for range in mutable_ranges {
                collect_pointer_bound_variables(&range.base, variables);
                collect_bitvector_bound_variables(&range.start, variables);
                collect_bitvector_bound_variables(&range.end, variables);
            }
        }
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => {
            collect_memory_bound_variables(before, variables);
            collect_memory_bound_variables(after, variables);
            collect_pointer_bound_variables(allocation_base, variables);
            collect_bitvector_bound_variables(bytes, variables);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bound_variables(left, variables);
            collect_proposition_bound_variables(right, variables);
        }
        Proposition::Not(body) => collect_proposition_bound_variables(body, variables),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            variables.insert(*var);
            collect_proposition_bound_variables(body, variables);
        }
    }
}

fn collect_term_bound_variables(term: &Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Term::Condition(condition) => collect_condition_bound_variables(condition, variables),
        Term::Bitvector32(bits) => collect_bitvector_bound_variables(bits, variables),
        Term::Integer(integer) => collect_integer_bound_variables(integer, variables),
        Term::PointerOffset(offset) => collect_pointer_offset_bound_variables(offset, variables),
        Term::CValue(value) => collect_c_value_bound_variables(value, variables),
        Term::Sequence(sequence) => collect_sequence_bound_variables(sequence, variables),
        Term::Algebraic(term) => collect_algebraic_bound_variables(term, variables),
        Term::CExpressionOutcome(outcome) => {
            collect_expression_outcome_bound_variables(outcome, variables)
        }
        Term::CStatementOutcome(outcome) => {
            collect_statement_outcome_bound_variables(outcome, variables)
        }
        Term::CFunctionOutcome(outcome) => {
            collect_function_outcome_bound_variables(outcome, variables)
        }
        Term::CState(state) => collect_c_state_bound_variables(state, variables),
        Term::CMemory(memory) => collect_memory_bound_variables(memory, variables),
    }
}

fn collect_sequence_bound_variables(sequence: &SequenceTerm, variables: &mut BTreeSet<Variable>) {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for value in values.iter() {
                collect_c_value_bound_variables(value, variables);
            }
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_bound_variables(left, variables);
            collect_sequence_bound_variables(right, variables);
        }
    }
}

fn collect_c_value_bound_variables(value: &CValue, variables: &mut BTreeSet<Variable>) {
    match value {
        CValue::Bool(bits)
        | CValue::Int16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::UInt32(bits)
        | CValue::Int64(bits)
        | CValue::UInt64(bits)
        | CValue::Float32(bits)
        | CValue::Float64(bits) => collect_bitvector_bound_variables(bits, variables),
        CValue::Pointer(pointer) => collect_pointer_bound_variables(pointer, variables),
        CValue::Void => {}
    }
}

fn collect_algebraic_value_bound_variables(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        AlgebraicValue::C(value) => collect_c_value_bound_variables(value, variables),
        AlgebraicValue::Integer(value) => collect_integer_bound_variables(value, variables),
        AlgebraicValue::Algebraic(value) => collect_algebraic_bound_variables(value, variables),
    }
}

fn collect_c_expression_bound_variables(
    expression: &CExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        CExpression::Value(value) => collect_c_value_bound_variables(value, variables),
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. } => {
            collect_c_expression_bound_variables(expression, variables);
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bound_variables(condition, variables);
            collect_c_expression_bound_variables(then_branch, variables);
            collect_c_expression_bound_variables(else_branch, variables);
        }
        CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. } => {
            collect_c_expression_bound_variables(expression, variables);
        }
        CExpression::AddressOf(body)
        | CExpression::Not(body)
        | CExpression::Load(body)
        | CExpression::BitwiseNot(body) => collect_c_expression_bound_variables(body, variables),
        CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_bound_variables(pointer, variables)
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            collect_c_expression_bound_variables(left, variables);
            collect_c_expression_bound_variables(right, variables);
        }
    }
}

pub(in crate::kernel) fn collect_c_statement_bound_variables(
    statement: &CStatement,
    variables: &mut BTreeSet<Variable>,
) {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => {}
        CStatement::ContinueWithStep { step } => {
            collect_c_statement_bound_variables(step, variables);
        }
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        } => collect_c_expression_bound_variables(expression, variables),
        CStatement::CallAssign { arguments, .. } | CStatement::Call { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
        }
        CStatement::HeapAllocate { bytes, .. } => {
            collect_c_expression_bound_variables(bytes, variables)
        }
        CStatement::HeapFree { pointer } => {
            collect_c_expression_bound_variables(pointer, variables)
        }
        CStatement::Seq(first, second) => {
            collect_c_statement_bound_variables(first, variables);
            collect_c_statement_bound_variables(second, variables);
        }
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            collect_c_expression_bound_variables(pointer, variables);
            collect_c_expression_bound_variables(value, variables);
        }
        CStatement::CopyAggregate { target, source, .. } => {
            collect_c_expression_bound_variables(target, variables);
            collect_c_expression_bound_variables(source, variables);
        }
        CStatement::Update {
            target, operand, ..
        } => {
            collect_c_expression_bound_variables(target, variables);
            collect_c_expression_bound_variables(operand, variables);
        }
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_bound_variables(condition, variables);
            collect_c_statement_bound_variables(then_branch, variables);
            collect_c_statement_bound_variables(else_branch, variables);
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            body,
            ..
        } => {
            collect_c_expression_bound_variables(condition, variables);
            for proposition in invariant {
                collect_proposition_bound_variables(proposition, variables);
            }
            for check in invariant_checks {
                collect_spec_proposition_bound_variables(check.proposition(), variables);
            }
            for check in effect_checks {
                collect_loop_effect_bound_variables(check.effect(), variables);
            }
            collect_c_statement_bound_variables(body, variables);
        }
        CStatement::Switch { expression, cases } => {
            collect_c_expression_bound_variables(expression, variables);
            for case in cases {
                collect_c_statement_bound_variables(&case.body, variables);
            }
        }
    }
}

fn collect_loop_effect_bound_variables(effect: &CLoopEffect, variables: &mut BTreeSet<Variable>) {
    if let CLoopEffect::Mutable(segments) = effect {
        for segment in segments {
            collect_c_memory_segment_bound_variables(segment, variables);
        }
    }
}

fn collect_c_memory_segment_bound_variables(
    segment: &CMemorySegment,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_expression_bound_variables(&segment.base, variables);
    collect_c_expression_bound_variables(&segment.start, variables);
    collect_c_expression_bound_variables(&segment.end, variables);
    if let Some(guard) = segment.guard() {
        collect_spec_proposition_bound_variables(guard, variables);
    }
}

pub(in crate::kernel) fn collect_c_state_bound_variables(
    state: &CState,
    variables: &mut BTreeSet<Variable>,
) {
    for binding in state.locals.bindings.values() {
        if let CLocalBinding::Object { value, .. } = binding {
            collect_c_value_bound_variables(value, variables);
        }
    }
    collect_memory_bound_variables(&state.memory, variables);
    for fact in state.resources.facts() {
        collect_resource_bound_variables(fact.resource(), variables);
    }
    for population in state.counted_populations.iter() {
        for argument in population.arguments.iter() {
            collect_algebraic_value_bound_variables(argument, variables);
        }
        collect_bitvector_bound_variables(&population.count, variables);
    }
}

pub(in crate::kernel) fn collect_statement_outcome_bound_variables(
    outcome: &CStatementOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CStatementOutcome::Normal(state)
        | CStatementOutcome::Break(state)
        | CStatementOutcome::Continue(state) => collect_c_state_bound_variables(state, variables),
        CStatementOutcome::Return { value, state } => {
            collect_c_value_bound_variables(value, variables);
            collect_c_state_bound_variables(state, variables);
        }
        CStatementOutcome::VerificationDiverges
        | CStatementOutcome::UndefinedBehavior(_)
        | CStatementOutcome::RuntimeError(_) => {}
    }
}

fn collect_function_outcome_bound_variables(
    outcome: &CFunctionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        CFunctionOutcome::Return { value, state } => {
            collect_c_value_bound_variables(value, variables);
            collect_c_state_bound_variables(state, variables);
        }
        CFunctionOutcome::VerificationDiverges
        | CFunctionOutcome::UndefinedBehavior(_)
        | CFunctionOutcome::RuntimeError(_) => {}
    }
}

fn collect_spec_proposition_bound_variables(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ExistsPointer { variable, body, .. } => {
            variables.insert(*variable);
            collect_spec_proposition_bound_variables(body, variables);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            collect_spec_proposition_bound_variables(left, variables);
            collect_spec_proposition_bound_variables(right, variables);
        }
        SpecProposition::Not(body) => collect_spec_proposition_bound_variables(body, variables),
        _ => {}
    }
}

fn collect_c_resource_spec_bound_variables(
    resource: &CResourceSpec,
    variables: &mut BTreeSet<Variable>,
) {
    match resource.term() {
        CResourceTerm::Instance { resource, .. } => {
            collect_c_resource_term_bound_variables(resource, variables)
        }
        CResourceTerm::Memory(segment) => {
            collect_c_memory_segment_bound_variables(segment, variables)
        }
        CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
        }
    }
    if let CResourceQuantity::Count(quantity) = resource.quantity() {
        collect_c_expression_bound_variables(quantity, variables);
    }
}

fn collect_c_resource_term_bound_variables(
    resource: &CResourceTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        CResourceTerm::Instance { resource, .. } => {
            collect_c_resource_term_bound_variables(resource, variables)
        }
        CResourceTerm::Memory(segment) => {
            collect_c_memory_segment_bound_variables(segment, variables)
        }
        CResourceTerm::Composite { arguments, .. } | CResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_c_function_bound_variables(
    function: &CFunction,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_function_contract_interface_bound_variables(function.contract_interface(), variables);
    collect_c_statement_bound_variables(function.body(), variables);
}

/// Collects only bound variables in the body-independent contract interface.
/// This is the companion to the bitvector collector used for named callback
/// contracts; no template statement or storage is traversed.
pub(in crate::kernel) fn collect_c_function_contract_interface_bound_variables(
    interface: &CFunctionContractInterface,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in interface
        .proof_parameters()
        .iter()
        .chain(interface.resource_requires())
        .chain(interface.resource_ensures())
        .chain(interface.resource_constructors())
    {
        collect_c_resource_spec_bound_variables(resource, variables);
    }
    for proposition in interface
        .contract_requires()
        .iter()
        .chain(interface.contract_ensures())
    {
        collect_spec_proposition_bound_variables(proposition, variables);
    }
    for segment in interface.contract_mutable() {
        collect_c_memory_segment_bound_variables(segment, variables);
    }
}

fn collect_c_function_specification_bound_variables(
    specification: &CFunctionSpecification,
    variables: &mut BTreeSet<Variable>,
) {
    collect_c_state_bound_variables(specification.state(), variables);
    for argument in specification.arguments() {
        collect_c_expression_bound_variables(argument, variables);
    }
    for requirement in specification.requires() {
        collect_proposition_bound_variables(requirement, variables);
    }
    collect_function_outcome_bound_variables(specification.outcome(), variables);
}

fn collect_expression_outcome_bound_variables(
    outcome: &CExpressionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    if let CExpressionOutcome::Value(value) = outcome {
        collect_c_value_bound_variables(value, variables);
    }
}

fn collect_pointer_bound_variables(pointer: &Pointer, variables: &mut BTreeSet<Variable>) {
    match &pointer.block {
        PointerBlock::FunctionSymbolic(variable) | PointerBlock::Symbolic(variable) => {
            variables.insert(*variable);
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::Heap(_) => {}
    }
    collect_pointer_offset_bound_variables(&pointer.offset, variables);
}

fn collect_memory_bound_variables(memory: &CMemory, variables: &mut BTreeSet<Variable>) {
    for contents in memory.blocks.values() {
        collect_bitvector_bound_variables(contents.size(), variables);
    }
    for (pointer, value) in memory.cells.as_ref() {
        collect_pointer_bound_variables(pointer, variables);
        collect_c_value_bound_variables(value, variables);
    }
}

fn collect_resource_bound_variables(resource: &CResource, variables: &mut BTreeSet<Variable>) {
    match resource {
        CResource::Instance(instance) => {
            for value in instance.arguments.iter().chain(instance.fields.iter()) {
                collect_algebraic_value_bound_variables(value, variables);
            }
        }
        CResource::Memory(range) => {
            collect_pointer_bound_variables(&range.base, variables);
            collect_bitvector_bound_variables(&range.start, variables);
            collect_bitvector_bound_variables(&range.end, variables);
        }
        CResource::Composite { arguments, .. } | CResource::Token { arguments, .. } => {
            for argument in arguments.iter() {
                collect_algebraic_value_bound_variables(argument, variables);
            }
        }
    }
}

/// Collects identities introduced by `RangeFold` binders inside a term.
/// `collect_bitvector_variables` intentionally removes those identities from
/// its result because they are not free; freshness construction needs the
/// bound identities as well so a logical or fold binder cannot reuse one.
fn collect_bitvector_bound_variables(term: &Bitvector32Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_bitvector_bound_variables(left, variables);
            collect_bitvector_bound_variables(right, variables);
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => {
            collect_bitvector_bound_variables(value, variables);
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bound_variables(condition, variables);
            collect_bitvector_bound_variables(then_term, variables);
            collect_bitvector_bound_variables(else_term, variables);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_bound_variables(start, variables);
            collect_bitvector_bound_variables(end, variables);
            collect_bitvector_bound_variables(initial, variables);
            variables.insert(*accumulator);
            variables.insert(*item);
            collect_bitvector_bound_variables(body, variables);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_bound_variables(argument, variables);
            }
        }
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                match argument {
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_bound_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(term) => {
                        collect_algebraic_bound_variables(term, variables)
                    }
                    PureFunctionArgument::Integer(_) => {}
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bound_variables(memory, variables);
                        collect_c_value_bound_variables(pointer, variables);
                    }
                }
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_bound_variables(scrutinee, variables);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_variables(binding, variables);
                }
                collect_bitvector_bound_variables(&arm.body, variables);
            }
        }
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            // Memory snapshots are immutable kernel values; their free
            // variable collector remains the source of truth for snapshot
            // contents, while the pointer can contain nested fold terms.
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
        Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_integer_bound_variables(value, variables);
        }
        Bitvector32Term::Int64Constant(_) | Bitvector32Term::UInt64Constant(_) => {}
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value) => {
            collect_bitvector_bound_variables(value, variables)
        }
        Bitvector32Term::Int64Add(left, right)
        | Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::Int64Divide(left, right)
        | Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64Add(left, right)
        | Bitvector32Term::UInt64Subtract(left, right)
        | Bitvector32Term::UInt64Multiply(left, right)
        | Bitvector32Term::UInt64Divide(left, right)
        | Bitvector32Term::UInt64Remainder(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right)
        | Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_bitvector_bound_variables(left, variables);
            collect_bitvector_bound_variables(right, variables);
        }
    }
}

fn collect_algebraic_bound_variables(term: &AlgebraicTerm, variables: &mut BTreeSet<Variable>) {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => {
            // Algebraic variables share the kernel identity namespace with
            // scalar variables and binders. Freshness must reserve them too.
            variables.insert(*variable);
        }
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_bound_variables(field, variables);
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_bound_variables(scrutinee, variables);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_variables(binding, variables);
                }
                collect_algebraic_bound_variables(&arm.body, variables);
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                match argument {
                    PureFunctionArgument::Value(value) => {
                        collect_c_value_bound_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(term) => {
                        collect_algebraic_bound_variables(term, variables)
                    }
                    PureFunctionArgument::Integer(_) => {}
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bound_variables(memory, variables);
                        collect_c_value_bound_variables(pointer, variables);
                    }
                }
            }
        }
    }
}

fn collect_condition_bound_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            left.for_each_bitvector_term(|term| collect_bitvector_bound_variables(term, variables));
            right
                .for_each_bitvector_term(|term| collect_bitvector_bound_variables(term, variables));
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64Equal(left, right)
        | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            collect_bitvector_bound_variables(left, variables);
            collect_bitvector_bound_variables(right, variables);
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            collect_integer_bound_variables(left, variables);
            collect_integer_bound_variables(right, variables);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_bound_variables(term, variables));
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_bound_variables(left, variables);
            collect_pointer_offset_bound_variables(right, variables);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_offset_bound_variables(&left.offset, variables);
            collect_pointer_offset_bound_variables(&right.offset, variables);
        }
    }
}

fn collect_pointer_offset_bound_variables(
    offset: &PointerOffsetTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_bound_variables(left, variables);
            collect_pointer_offset_bound_variables(right, variables);
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_bound_variables(value, variables);
        }
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_term(
    term: &Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Term {
    match term {
        Term::Condition(condition) => Term::Condition(substitute_bitvector_variable_in_condition(
            condition, from, to,
        )),
        Term::Bitvector32(bits) => Term::Bitvector32(substitute_bitvector_variable(bits, from, to)),
        // Variable identities are shared by all logical sorts, but a
        // machine substitution must never rewrite an Integer variable with a
        // machine term. Integer binders use the dedicated function below.
        Term::Integer(integer) => {
            Term::Integer(substitute_bitvector_variable_in_integer(integer, from, to))
        }
        Term::PointerOffset(offset) => Term::PointerOffset(
            substitute_bitvector_variable_in_pointer_offset(offset, from, to),
        ),
        Term::CValue(value) => {
            Term::CValue(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        Term::Sequence(sequence) => Term::Sequence(substitute_bitvector_variable_in_sequence(
            sequence, from, to,
        )),
        Term::Algebraic(term) => Term::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: match &term.node {
                AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
                AlgebraicTermNode::Constructor { variant, fields } => {
                    AlgebraicTermNode::Constructor {
                        variant: variant.clone(),
                        fields: fields
                            .iter()
                            .map(|field| {
                                substitute_bitvector_variable_in_algebraic_value(field, from, to)
                            })
                            .collect(),
                    }
                }
                AlgebraicTermNode::Match { scrutinee, arms } => AlgebraicTermNode::Match {
                    scrutinee: Box::new(substitute_bitvector_variable_in_algebraic_term(
                        scrutinee, from, to,
                    )),
                    arms: arms
                        .iter()
                        .map(|arm| AlgebraicResultMatchArm {
                            variant: arm.variant.clone(),
                            bindings: arm
                                .bindings
                                .iter()
                                .map(|binding| {
                                    substitute_bitvector_variable_in_algebraic_value(
                                        binding, from, to,
                                    )
                                })
                                .collect(),
                            body: substitute_bitvector_variable_in_algebraic_term(
                                &arm.body, from, to,
                            ),
                        })
                        .collect(),
                },
                AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                    AlgebraicTermNode::PureFunctionApplication {
                        name: name.clone(),
                        arguments: arguments
                            .iter()
                            .map(|argument| {
                                substitute_bitvector_variable_in_pure_function_argument(
                                    argument, from, to,
                                )
                            })
                            .collect(),
                    }
                }
            },
        }),
        Term::CExpressionOutcome(outcome) => Term::CExpressionOutcome(
            substitute_bitvector_variable_in_c_expression_outcome(outcome, from, to),
        ),
        Term::CStatementOutcome(outcome) => Term::CStatementOutcome(
            substitute_bitvector_variable_in_c_statement_outcome(outcome, from, to),
        ),
        Term::CFunctionOutcome(outcome) => Term::CFunctionOutcome(
            substitute_bitvector_variable_in_c_function_outcome(outcome, from, to),
        ),
        Term::CMemory(memory) => {
            Term::CMemory(substitute_bitvector_variable_in_memory(memory, from, to))
        }
        Term::CState(state) => {
            Term::CState(substitute_bitvector_variable_in_c_state(state, from, to))
        }
    }
}

fn substitute_bitvector_variable_in_integer(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> IntegerTerm {
    match substitute_bitvector_variable_in_integer_checked(term, from, to) {
        Ok(result) => result,
        Err(_) => term.clone(),
    }
}

fn substitute_bitvector_variable_in_integer_checked(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    substitute_bitvector_variable_in_integer_checked_with_mode(term, from, to, false)
}

fn substitute_bitvector_variable_in_integer_checked_with_registered_loads(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    substitute_bitvector_variable_in_integer_checked_with_mode(term, from, to, true)
}

fn substitute_bitvector_variable_in_integer_checked_with_mode(
    term: &IntegerTerm,
    from: Variable,
    to: &Bitvector32Term,
    resolve_registered_loads: bool,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let source = Bitvector32Term::Variable(from);
    let mut rewrite =
        crate::kernel::proof::term_rewrite::TermRewrite::for_bits_checked(&source, to);
    if resolve_registered_loads {
        rewrite.enable_registered_load_resolution();
    }
    let result = match rewrite.term(&Term::Integer(term.clone())) {
        Term::Integer(result) => result,
        _ => unreachable!(),
    };
    if rewrite.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    if rewrite.unsupported_integer_scope {
        return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
    }
    Ok(result)
}

pub(in crate::kernel) fn collect_integer_bound_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = BTreeSet::new();
    collect_integer_bound_variables_seen(term, variables, &mut seen);
}

fn collect_integer_bound_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut BTreeSet<u64>,
) {
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Machine(_) => {}
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if let PureFunctionArgument::Integer(value) = argument
                    && seen.insert(value.id())
                {
                    collect_integer_bound_variables_seen(value, variables, seen);
                }
            }
        }
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::Negate(value) => {
            if seen.insert(value.id()) {
                collect_integer_bound_variables_seen(value, variables, seen);
            }
        }
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            if seen.insert(left.id()) {
                collect_integer_bound_variables_seen(left, variables, seen);
            }
            if seen.insert(right.id()) {
                collect_integer_bound_variables_seen(right, variables, seen);
            }
        }
        IntegerTerm::AlgebraicMatch { .. } => {
            // The algebraic scrutinee and arm declarations can carry C or
            // Integer expressions; use the established carrier-aware walker
            // for this shared namespace instead of dropping either side.
            crate::kernel::prelude::collect_integer_variables(term, variables);
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end } => {
                    collect_bitvector_variables(start.value(), variables);
                    collect_bitvector_variables(end.value(), variables);
                }
                crate::kernel::IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_integer_bound_variables_seen(start, variables, seen);
                    collect_integer_bound_variables_seen(end, variables, seen);
                }
            }
            collect_integer_bound_variables_seen(initial, variables, seen);
            let mut body_variables = BTreeSet::new();
            collect_integer_bound_variables_seen(body, &mut body_variables, &mut BTreeSet::new());
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
    }
}

/// The proposition fragment accepted by checked mathematical-integer
/// instantiation.  Integer binders are deliberately kept separate from the
/// machine and resource proposition carriers: cloning an unsupported carrier
/// here would make a proof object appear instantiated while leaving an
/// occurrence of the old variable behind.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IntegerPureSubstitutionError {
    UnsupportedCarrier,
    UnsupportedSort,
    FreshVariableExhausted,
    WorkLimitExceeded,
}

/// Capture-avoiding substitution for the complete pure Integer proposition
/// fragment. Validation collects the source once, and replacement uses one
/// carrier-aware walker. Its scoped Integer map gives nested binders lexical
/// scope without cloning a complete suffix environment for every binder.
pub(crate) fn substitute_integer_variable_in_pure_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &IntegerTerm,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    let mut reserved = BTreeSet::new();
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::checked();
    // Traverse the replacement once, then charge only the shallow root copy
    // at each occurrence. Shared descendants are not copied by substitution.
    // `validate_integer_pure_term` uses the checked carrier collector, so the
    // replacement's selected registered-load pointers are included in this
    // one setup traversal without scanning their snapshots.
    validate_integer_pure_term(to, &mut reserved, &mut collector)?;
    validate_integer_pure_proposition(proposition, &mut reserved, &mut collector)?;
    if collector.exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    collector.extend_into(&mut reserved);
    reserved.insert(from);
    // The general proposition walker intentionally stops at binder-bearing
    // propositions.  Keep one checked walker for all atomic leaves instead
    // of rebuilding its replacement summary and fresh allocator per leaf.
    // The lexical Integer scope is pushed and popped by the recursive
    // proposition traversal below.
    let renamings = BTreeMap::new();
    let mut walker = crate::kernel::proof::term_rewrite::TermRewrite::for_integer_variables(
        from, to, false, &renamings,
    );
    // A symbolic C load is represented by a registered load variable.  The
    // selected pointer is part of the source expression for this checked
    // witness substitution, so let the shared walker remint that load at the
    // rewritten cell while retaining its original snapshot.
    walker.enable_registered_load_resolution();
    walker.reserve_integer_substitution_variables(&reserved);
    let result =
        substitute_integer_pure_proposition_with_walker(proposition, from, false, &mut walker);
    if walker.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    if walker.unsupported_integer_scope {
        return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
    }
    result
}

fn integer_work(units: usize) -> Result<(), IntegerPureSubstitutionError> {
    if crate::instrumentation::deadline_exceeded_with_work(units) {
        Err(IntegerPureSubstitutionError::WorkLimitExceeded)
    } else {
        Ok(())
    }
}

fn validate_integer_pure_proposition(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    integer_work(1)?;
    match proposition {
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => {
            validate_integer_pure_term(left, variables, collector)?;
            validate_integer_pure_term(right, variables, collector)?;
            Ok(())
        }
        Proposition::Equal(left, right)
            if integer_atomic_term_supported(left) && integer_atomic_term_supported(right) =>
        {
            validate_integer_atomic_proposition(proposition, collector)
        }
        Proposition::ConditionIs(condition, _) => {
            validate_integer_pure_condition(condition, collector)
        }
        Proposition::CMemoryLoadable { .. } => {
            // A symbolic array read contributes this obligation to the
            // existential body.  It is a supported C carrier as long as its
            // pointer and byte-count expressions are rewritten by the same
            // checked walker; the memory snapshot remains opaque.
            integer_work(1)?;
            collector.collect(proposition);
            if collector.exhausted() {
                return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
            }
            Ok(())
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            validate_integer_pure_proposition(left, variables, collector)?;
            validate_integer_pure_proposition(right, variables, collector)
        }
        Proposition::Not(body) => validate_integer_pure_proposition(body, variables, collector),
        Proposition::ForAll { var, sort, body } => {
            if !matches!(
                sort,
                Sort::Integer | Sort::CInt32 | Sort::CInt64 | Sort::CPointer(_)
            ) {
                return Err(IntegerPureSubstitutionError::UnsupportedSort);
            }
            variables.insert(*var);
            validate_integer_pure_proposition(body, variables, collector)
        }
        Proposition::Exists {
            var, sort, body, ..
        } => {
            if !matches!(
                sort,
                Sort::Integer | Sort::CInt32 | Sort::CInt64 | Sort::CPointer(_)
            ) {
                return Err(IntegerPureSubstitutionError::UnsupportedSort);
            }
            variables.insert(*var);
            validate_integer_pure_proposition(body, variables, collector)
        }
        _ => Err(IntegerPureSubstitutionError::UnsupportedCarrier),
    }
}

fn validate_integer_pure_condition(
    condition: &ConditionTerm,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    validate_integer_atomic_proposition(
        &Proposition::ConditionIs(condition.clone(), true),
        collector,
    )
}

fn validate_integer_pure_term(
    term: &IntegerTerm,
    _variables: &mut BTreeSet<Variable>,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    validate_integer_atomic_proposition(
        &Proposition::Equal(
            Term::Integer(term.clone()),
            Term::Integer(IntegerTerm::constant_i64(0)),
        ),
        collector,
    )
}

fn validate_integer_atomic_proposition(
    proposition: &Proposition,
    collector: &mut crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector,
) -> Result<(), IntegerPureSubstitutionError> {
    rewrite_integer_atomic_proposition(
        proposition,
        Variable(0),
        &IntegerTerm::constant_i64(0),
        true,
        &BTreeMap::new(),
    )?;
    collector.collect(proposition);
    if collector.exhausted() {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    Ok(())
}

fn rewrite_integer_atomic_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &IntegerTerm,
    shadowed: bool,
    renamings: &BTreeMap<Variable, Variable>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    integer_work(1)?;
    let mut walker = crate::kernel::proof::term_rewrite::TermRewrite::for_integer_variables(
        from, to, shadowed, renamings,
    );
    let result = walker.proposition(proposition);
    if walker.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    if walker.unsupported_integer_scope {
        return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
    }
    integer_work(0)?;
    Ok(result)
}

fn rewrite_integer_atomic_proposition_with_walker(
    proposition: &Proposition,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    integer_work(1)?;
    let result = walker.proposition(proposition);
    if walker.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    if walker.unsupported_integer_scope {
        return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
    }
    integer_work(0)?;
    Ok(result)
}

/// Recursive proposition traversal for checked Integer substitution.  The
/// caller supplies one walker for the whole proposition.  In particular, the
/// replacement's carrier summary, DAG cache, fresh allocator, and work state
/// are shared across sibling atomic propositions.
fn substitute_integer_pure_proposition_with_walker(
    proposition: &Proposition,
    from: Variable,
    shadowed: bool,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    integer_work(1)?;
    match proposition {
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => Ok(Proposition::Equal(
            Term::Integer(substitute_integer_pure_term_with_walker(left, walker)?),
            Term::Integer(substitute_integer_pure_term_with_walker(right, walker)?),
        )),
        Proposition::Equal(left, right)
            if integer_atomic_term_supported(left) && integer_atomic_term_supported(right) =>
        {
            rewrite_integer_atomic_proposition_with_walker(proposition, walker)
        }
        Proposition::ConditionIs(condition, value) => Ok(Proposition::ConditionIs(
            substitute_integer_pure_condition_with_walker(condition, walker)?,
            *value,
        )),
        Proposition::CMemoryLoadable { .. } => {
            rewrite_integer_memory_loadable_with_walker(proposition, walker)
        }
        Proposition::And(left, right) => Ok(Proposition::And(
            Box::new(substitute_integer_pure_proposition_with_walker(
                left, from, shadowed, walker,
            )?),
            Box::new(substitute_integer_pure_proposition_with_walker(
                right, from, shadowed, walker,
            )?),
        )),
        Proposition::Or(left, right) => Ok(Proposition::Or(
            Box::new(substitute_integer_pure_proposition_with_walker(
                left, from, shadowed, walker,
            )?),
            Box::new(substitute_integer_pure_proposition_with_walker(
                right, from, shadowed, walker,
            )?),
        )),
        Proposition::Not(body) => Ok(Proposition::Not(Box::new(
            substitute_integer_pure_proposition_with_walker(body, from, shadowed, walker)?,
        ))),
        Proposition::Implies(left, right) => Ok(Proposition::Implies(
            Box::new(substitute_integer_pure_proposition_with_walker(
                left, from, shadowed, walker,
            )?),
            Box::new(substitute_integer_pure_proposition_with_walker(
                right, from, shadowed, walker,
            )?),
        )),
        Proposition::ForAll { var, sort, body } => substitute_integer_quantifier_with_walker(
            false, None, *var, sort, body, from, shadowed, walker,
        ),
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } => substitute_integer_quantifier_with_walker(
            true,
            Some(name),
            *var,
            sort,
            body,
            from,
            shadowed,
            walker,
        ),
        _ => Err(IntegerPureSubstitutionError::UnsupportedCarrier),
    }
}

// Keep the proposition's carrier and lexical state explicit at this boundary;
// hiding them in a mutable context would make it easier to apply a scope to
// the replacement rather than to the source body.
#[allow(clippy::too_many_arguments)]
fn substitute_integer_quantifier_with_walker(
    exists: bool,
    name: Option<&String>,
    var: Variable,
    sort: &Sort,
    body: &Proposition,
    from: Variable,
    shadowed: bool,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    let is_integer = *sort == Sort::Integer;
    let is_c = matches!(sort, Sort::CInt32 | Sort::CInt64 | Sort::CPointer(_));
    if !is_integer && !is_c {
        return Err(IntegerPureSubstitutionError::UnsupportedSort);
    }

    let renamed = if is_integer {
        !shadowed && var != from && walker.replacement_contains_integer_variable(var)
    } else {
        walker.replacement_contains_c_variable(var)
    };
    if walker.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    let new_var = if renamed {
        let Some(variable) = walker.fresh_integer_substitution_variable() else {
            return if walker.integer_work_exhausted {
                Err(IntegerPureSubstitutionError::WorkLimitExceeded)
            } else {
                Err(IntegerPureSubstitutionError::FreshVariableExhausted)
            };
        };
        variable
    } else {
        var
    };
    if walker.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }

    let transformed = if is_integer {
        let scope = walker.push_integer_substitution_scope(var, new_var, shadowed || var == from);
        let transformed = substitute_integer_pure_proposition_with_walker(
            body,
            from,
            shadowed || var == from,
            walker,
        );
        walker.pop_integer_substitution_scope(scope);
        transformed
    } else {
        let scope = walker.push_c_substitution_scope(var, new_var);
        let transformed =
            substitute_integer_pure_proposition_with_walker(body, from, shadowed, walker);
        walker.pop_c_substitution_scope(scope);
        transformed
    }?;
    if exists {
        Ok(Proposition::Exists {
            name: name.cloned().unwrap_or_default(),
            var: new_var,
            sort: sort.clone(),
            body: Box::new(transformed),
        })
    } else {
        Ok(Proposition::ForAll {
            var: new_var,
            sort: sort.clone(),
            body: Box::new(transformed),
        })
    }
}

fn substitute_integer_pure_condition_with_walker(
    condition: &ConditionTerm,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<ConditionTerm, IntegerPureSubstitutionError> {
    let Proposition::ConditionIs(result, _) = rewrite_integer_atomic_proposition_with_walker(
        &Proposition::ConditionIs(condition.clone(), true),
        walker,
    )?
    else {
        unreachable!()
    };
    Ok(result)
}

fn rewrite_integer_memory_loadable_with_walker(
    proposition: &Proposition,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<Proposition, IntegerPureSubstitutionError> {
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
    } = proposition
    else {
        unreachable!("memory-loadable helper called for another proposition carrier")
    };
    integer_work(1)?;
    let pointer = CValue::Pointer(CPointerValue::new(base.clone(), CType::VoidPointer));
    let Term::CValue(CValue::Pointer(pointer)) = walker.term(&Term::CValue(pointer)) else {
        unreachable!("pointer rewrite changed its carrier")
    };
    if walker.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    let bytes = walker.bits(bytes);
    if walker.integer_work_exhausted {
        return Err(IntegerPureSubstitutionError::WorkLimitExceeded);
    }
    if walker.unsupported_integer_scope {
        return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
    }
    Ok(Proposition::CMemoryLoadable {
        // Snapshots are immutable proof-state identities.  Keep the same
        // handle and rewrite only the selected address/width expressions.
        memory: memory.clone(),
        base: pointer.pointer().clone(),
        bytes,
    })
}

fn substitute_integer_pure_term_with_walker(
    term: &IntegerTerm,
    walker: &mut crate::kernel::proof::term_rewrite::TermRewrite<'_>,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let Proposition::Equal(Term::Integer(result), _) =
        rewrite_integer_atomic_proposition_with_walker(
            &Proposition::Equal(
                Term::Integer(term.clone()),
                Term::Integer(IntegerTerm::constant_i64(0)),
            ),
            walker,
        )?
    else {
        unreachable!()
    };
    Ok(result)
}

fn integer_atomic_term_supported(term: &Term) -> bool {
    matches!(
        term,
        Term::Integer(_)
            | Term::Bitvector32(_)
            | Term::CValue(_)
            | Term::Algebraic(_)
            | Term::Condition(_)
            | Term::PointerOffset(_)
    )
}

fn substitute_integer_pure_term(
    term: &IntegerTerm,
    from: Variable,
    to: &IntegerTerm,
    shadowed: bool,
    renamings: &BTreeMap<Variable, Variable>,
    _replacement_work: usize,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let Proposition::Equal(Term::Integer(result), _) = rewrite_integer_atomic_proposition(
        &Proposition::Equal(
            Term::Integer(term.clone()),
            Term::Integer(IntegerTerm::constant_i64(0)),
        ),
        from,
        to,
        shadowed,
        renamings,
    )?
    else {
        unreachable!()
    };
    Ok(result)
}

/// Instantiate one Integer fold step without expanding the surrounding
/// range. The two binders are substituted through the existing
/// capture-avoiding DAG walker, so a nested fold cannot capture either step
/// value.
#[allow(dead_code)]
pub(in crate::kernel) fn instantiate_integer_range_fold_step(
    body: &IntegerTerm,
    accumulator: Variable,
    accumulator_value: &IntegerTerm,
    item: Variable,
    item_value: &IntegerTerm,
    c_item: bool,
) -> Result<IntegerTerm, IntegerPureSubstitutionError> {
    let replacement_work = |term: &IntegerTerm| match term {
        IntegerTerm::Constant(value) => value.bits() as usize + 1,
        _ => 1,
    };
    let mut reserved = BTreeSet::new();
    collect_integer_carrier_variables(body, &mut reserved);
    collect_integer_capture_bitvector_variables(body, &mut reserved);
    collect_integer_carrier_variables(accumulator_value, &mut reserved);
    collect_integer_capture_bitvector_variables(accumulator_value, &mut reserved);
    collect_integer_carrier_variables(item_value, &mut reserved);
    collect_integer_capture_bitvector_variables(item_value, &mut reserved);
    let mut integer_binders = BTreeSet::new();
    let mut bitvector_binders = BTreeSet::new();
    collect_integer_binder_variables(body, &mut integer_binders, &mut bitvector_binders);
    collect_integer_binder_variables(
        accumulator_value,
        &mut integer_binders,
        &mut bitvector_binders,
    );
    collect_integer_binder_variables(item_value, &mut integer_binders, &mut bitvector_binders);
    reserved.extend(integer_binders);
    reserved.extend(bitvector_binders);
    reserved.insert(accumulator);
    reserved.insert(item);
    let mut generator = KernelVariableGenerator::fresh_for(0, reserved);
    let temporary = generator.next();
    let temporary_item = generator.next();
    let with_temporary = substitute_integer_pure_term(
        body,
        accumulator,
        &IntegerTerm::Variable(temporary),
        false,
        &BTreeMap::new(),
        1,
    )?;
    // Keep the two carriers separate.  An Int32 fold binds a machine
    // variable, while an Integer fold binds an Integer variable.  In
    // particular, substituting the Integer spelling of an Int32 binder would
    // leave the machine occurrence untouched (and trying both substitutions
    // would rewrite an unrelated Integer variable with the same identity).
    let with_item = if c_item {
        substitute_bitvector_variable_in_integer_checked_with_registered_loads(
            &with_temporary,
            item,
            &Bitvector32Term::Variable(temporary_item),
        )?
    } else {
        substitute_integer_pure_term(
            &with_temporary,
            item,
            &IntegerTerm::Variable(temporary_item),
            false,
            &BTreeMap::new(),
            1,
        )?
    };
    let with_accumulator = substitute_integer_pure_term(
        &with_item,
        temporary,
        accumulator_value,
        false,
        &BTreeMap::new(),
        replacement_work(accumulator_value),
    )?;
    if c_item {
        let Some(bits) = integer_item_bitvector(item_value) else {
            return Err(IntegerPureSubstitutionError::UnsupportedCarrier);
        };
        Ok(
            substitute_bitvector_variable_in_integer_checked_with_registered_loads(
                &with_accumulator,
                temporary_item,
                &bits,
            )?,
        )
    } else {
        substitute_integer_pure_term(
            &with_accumulator,
            temporary_item,
            item_value,
            false,
            &BTreeMap::new(),
            replacement_work(item_value),
        )
    }
}

fn integer_item_bitvector(value: &IntegerTerm) -> Option<Bitvector32Term> {
    match value {
        IntegerTerm::Machine(machine) if machine.ty() == MachineIntegerType::Int32 => {
            Some(machine.value().clone())
        }
        IntegerTerm::Constant(value) => value
            .to_i64()
            .filter(|value| (i64::from(i32::MIN)..=i64::from(i32::MAX)).contains(value))
            .map(|value| Bitvector32Term::Constant(value as i32 as u32)),
        _ => None,
    }
}

fn substitute_bitvector_variable_in_algebraic_term(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> AlgebraicTerm {
    let Term::Algebraic(term) =
        substitute_bitvector_variable_in_term(&Term::Algebraic(term.clone()), from, to)
    else {
        unreachable!()
    };
    term
}

fn substitute_bitvector_variable_in_algebraic_value(
    value: &AlgebraicValue,
    from: Variable,
    to: &Bitvector32Term,
) -> AlgebraicValue {
    match value {
        AlgebraicValue::C(value) => {
            AlgebraicValue::C(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        AlgebraicValue::Integer(value) => {
            AlgebraicValue::Integer(substitute_bitvector_variable_in_integer(value, from, to))
        }
        AlgebraicValue::Algebraic(value) => AlgebraicValue::Algebraic(
            substitute_bitvector_variable_in_algebraic_term(value, from, to),
        ),
    }
}

fn substitute_bitvector_variable_in_pure_function_argument(
    argument: &PureFunctionArgument,
    from: Variable,
    to: &Bitvector32Term,
) -> PureFunctionArgument {
    match argument {
        PureFunctionArgument::Integer(value) => PureFunctionArgument::Integer(
            substitute_bitvector_variable_in_integer(value.as_ref(), from, to).into(),
        ),
        PureFunctionArgument::Value(value) => {
            PureFunctionArgument::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        PureFunctionArgument::Algebraic(term) => PureFunctionArgument::Algebraic(
            substitute_bitvector_variable_in_algebraic_term(term, from, to),
        ),
        PureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => PureFunctionArgument::ArrayRef {
            memory: substitute_bitvector_variable_in_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_c_value(pointer, from, to),
            element_type: *element_type,
        },
    }
}

fn substitute_bitvector_variable_in_sequence(
    sequence: &SequenceTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> SequenceTerm {
    let node = match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => SequenceTermNode::Literal(
            values
                .iter()
                .map(|value| substitute_bitvector_variable_in_c_value(value, from, to))
                .collect::<Vec<_>>()
                .into(),
        ),
        SequenceTermNode::Concat(left, right) => SequenceTermNode::Concat(
            substitute_bitvector_variable_in_sequence(left, from, to),
            substitute_bitvector_variable_in_sequence(right, from, to),
        ),
    };
    SequenceTerm {
        element_type: sequence.element_type,
        node: std::sync::Arc::new(node),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_expression(
    expression: &CExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpression {
    match expression {
        CExpression::Value(value) => {
            CExpression::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        CExpression::Variable(name) => CExpression::Variable(name.clone()),
        CExpression::FunctionAddress(name) => CExpression::FunctionAddress(name.clone()),
        CExpression::Cast {
            expression,
            target_type,
            pointee_volatile,
            pointee_constant,
        } => CExpression::Cast {
            expression: Box::new(substitute_bitvector_variable_in_c_expression(
                expression, from, to,
            )),
            target_type: *target_type,
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
        },
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => CExpression::Conditional {
            condition: Box::new(substitute_bitvector_variable_in_c_expression(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_bitvector_variable_in_c_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_c_expression(
                else_branch,
                from,
                to,
            )),
        },
        CExpression::FloatClassification {
            expression,
            classification,
        } => CExpression::FloatClassification {
            expression: Box::new(substitute_bitvector_variable_in_c_expression(
                expression, from, to,
            )),
            classification: *classification,
        },
        CExpression::FloatNegate(expression) => CExpression::FloatNegate(Box::new(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        )),
        CExpression::AddressOf(body) => CExpression::AddressOf(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::PointerOffsetBytes { pointer, bytes } => CExpression::PointerOffsetBytes {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            bytes: *bytes,
        },
        CExpression::Not(body) => CExpression::Not(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::Load(body) => CExpression::Load(Box::new(
            substitute_bitvector_variable_in_c_expression(body, from, to),
        )),
        CExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
        } => CExpression::TypedLoad {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
            volatile: *volatile,
        },
        CExpression::LessThan(left, right) => CExpression::LessThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::LessEqual(left, right) => CExpression::LessEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterThan(left, right) => CExpression::GreaterThan(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::GreaterEqual(left, right) => CExpression::GreaterEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Equal(left, right) => CExpression::Equal(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::NotEqual(left, right) => CExpression::NotEqual(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::And(left, right) => CExpression::And(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Or(left, right) => CExpression::Or(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Add(left, right) => CExpression::Add(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Subtract(left, right) => CExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Multiply(left, right) => CExpression::Multiply(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Divide(left, right) => CExpression::Divide(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::Remainder(left, right) => CExpression::Remainder(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::ShiftLeft(left, right) => CExpression::ShiftLeft(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::ShiftRight(left, right) => CExpression::ShiftRight(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseAnd(left, right) => CExpression::BitwiseAnd(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseOr(left, right) => CExpression::BitwiseOr(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseXor(left, right) => CExpression::BitwiseXor(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
        CExpression::BitwiseNot(expression) => CExpression::BitwiseNot(Box::new(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        )),
        CExpression::Index(left, right) => CExpression::Index(
            Box::new(substitute_bitvector_variable_in_c_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_expression(
                right, from, to,
            )),
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_statement(
    statement: &CStatement,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatement {
    match statement {
        CStatement::Skip => CStatement::Skip,
        CStatement::Break => CStatement::Break,
        CStatement::Continue => CStatement::Continue,
        CStatement::ContinueWithStep { step } => CStatement::ContinueWithStep {
            step: Box::new(substitute_bitvector_variable_in_c_statement(step, from, to)),
        },
        CStatement::Declare {
            name,
            c_type,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        } => CStatement::Declare {
            name: name.clone(),
            c_type: *c_type,
            volatile: *volatile,
            pointee_volatile: *pointee_volatile,
            constant: *constant,
            pointee_constant: *pointee_constant,
        },
        CStatement::DeclareAggregate { name, layout } => CStatement::DeclareAggregate {
            name: name.clone(),
            layout: layout.clone(),
        },
        CStatement::Assign { name, expression } => CStatement::Assign {
            name: name.clone(),
            expression: substitute_bitvector_variable_in_c_expression(expression, from, to),
        },
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => CStatement::CallAssign {
            target: target.clone(),
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
        },
        CStatement::Call {
            function_name,
            arguments,
        } => CStatement::Call {
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
        },
        CStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
        } => CStatement::HeapAllocate {
            target: target.clone(),
            bytes: substitute_bitvector_variable_in_c_expression(bytes, from, to),
            zeroed: *zeroed,
        },
        CStatement::HeapFree { pointer } => CStatement::HeapFree {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
        },
        CStatement::Assert { condition, label } => CStatement::Assert {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            label: label.clone(),
        },
        CStatement::Seq(first, second) => c_seq(
            substitute_bitvector_variable_in_c_statement(first, from, to),
            substitute_bitvector_variable_in_c_statement(second, from, to),
        ),
        CStatement::Return(expression) => CStatement::Return(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        ),
        CStatement::Store { pointer, value } => CStatement::Store {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
            value: substitute_bitvector_variable_in_c_expression(value, from, to),
        },
        CStatement::TypedStore {
            pointer,
            value,
            value_type,
            volatile,
        } => CStatement::TypedStore {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
            value: substitute_bitvector_variable_in_c_expression(value, from, to),
            value_type: *value_type,
            volatile: *volatile,
        },
        CStatement::CopyAggregate {
            target,
            source,
            layout,
        } => CStatement::CopyAggregate {
            target: substitute_bitvector_variable_in_c_expression(target, from, to),
            source: substitute_bitvector_variable_in_c_expression(source, from, to),
            layout: layout.clone(),
        },
        CStatement::Update {
            target,
            operator,
            operand,
        } => CStatement::Update {
            target: substitute_bitvector_variable_in_c_expression(target, from, to),
            operator: *operator,
            operand: substitute_bitvector_variable_in_c_expression(operand, from, to),
        },
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => CStatement::If {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            then_branch: Box::new(substitute_bitvector_variable_in_c_statement(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_c_statement(
                else_branch,
                from,
                to,
            )),
        },
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            do_while,
        } => CStatement::While {
            structural_measure: structural_measure.clone(),
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            ranking_measures: ranking_measures
                .iter()
                .map(|measure| substitute_bitvector_variable_in_c_expression(measure, from, to))
                .collect(),
            resource_specs: resource_specs
                .iter()
                .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
                .collect(),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            invariant_checks: invariant_checks
                .iter()
                .map(|check| CLoopInvariantCheck {
                    proposition: substitute_bitvector_variable_in_spec_proposition(
                        check.proposition(),
                        from,
                        to,
                    ),
                    entry_context: check.entry_context.clone(),
                    preservation_context: check.preservation_context.clone(),
                })
                .collect(),
            effect_checks: effect_checks
                .iter()
                .map(|check| CLoopEffectCheck {
                    effect: substitute_bitvector_variable_in_loop_effect(check.effect(), from, to),
                    span: check.span,
                    context: check.context.clone(),
                    origin: check.origin,
                    validated_ranges: check.validated_ranges.as_ref().map(|ranges| {
                        ranges
                            .iter()
                            .map(|range| {
                                substitute_bitvector_variable_in_c_memory_range(range, from, to)
                            })
                            .collect()
                    }),
                })
                .collect(),
            do_while: *do_while,
            body: Box::new(substitute_bitvector_variable_in_c_statement(body, from, to)),
        },
        CStatement::Switch { expression, cases } => CStatement::Switch {
            expression: substitute_bitvector_variable_in_c_expression(expression, from, to),
            cases: cases
                .iter()
                .map(|case| CSwitchCase {
                    value: case.value,
                    body: Box::new(substitute_bitvector_variable_in_c_statement(
                        &case.body, from, to,
                    )),
                })
                .collect(),
        },
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_memory(
    memory: &SpecMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecMemory {
    match memory {
        SpecMemory::Current => SpecMemory::Current,
        SpecMemory::FunctionEntry => SpecMemory::FunctionEntry,
        SpecMemory::LoopEntry => SpecMemory::LoopEntry,
        SpecMemory::Fixed(memory) => {
            SpecMemory::Fixed(substitute_bitvector_variable_in_memory(memory, from, to))
        }
    }
}

fn substitute_bitvector_variable_in_spec_algebraic_expression(
    expression: &SpecAlgebraicExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecAlgebraicExpression {
    let node = match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(projection) => {
            SpecAlgebraicExpressionNode::ResourceField(projection.clone())
        }
        SpecAlgebraicExpressionNode::Variable(variable) => {
            SpecAlgebraicExpressionNode::Variable(*variable)
        }
        SpecAlgebraicExpressionNode::Binding(name) => {
            SpecAlgebraicExpressionNode::Binding(name.clone())
        }
        SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
            SpecAlgebraicExpressionNode::Constructor {
                variant: variant.clone(),
                fields: fields
                    .iter()
                    .map(|field| match field {
                        SpecAlgebraicValue::C(field) => SpecAlgebraicValue::C(
                            substitute_bitvector_variable_in_spec_expression(field, from, to),
                        ),
                        SpecAlgebraicValue::Integer(field) => {
                            SpecAlgebraicValue::Integer(field.clone())
                        }
                        SpecAlgebraicValue::Algebraic(field) => SpecAlgebraicValue::Algebraic(
                            substitute_bitvector_variable_in_spec_algebraic_expression(
                                field, from, to,
                            ),
                        ),
                    })
                    .collect(),
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            SpecAlgebraicExpressionNode::Match {
                scrutinee: Box::new(substitute_bitvector_variable_in_spec_algebraic_expression(
                    scrutinee, from, to,
                )),
                arms: arms
                    .iter()
                    .map(|arm| SpecAlgebraicResultMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        body: Box::new(substitute_bitvector_variable_in_spec_algebraic_expression(
                            &arm.body, from, to,
                        )),
                    })
                    .collect(),
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            SpecAlgebraicExpressionNode::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_bitvector_variable_in_spec_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
    };
    SpecAlgebraicExpression {
        algebraic_type: expression.algebraic_type.clone(),
        node,
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecExpression {
    match expression {
        SpecExpression::ResourceField { .. } => expression.clone(),
        SpecExpression::IntegerToMachine { value, destination } => {
            SpecExpression::IntegerToMachine {
                value: Box::new(substitute_bitvector_variable_in_spec_integer(
                    value, from, to,
                )),
                destination: *destination,
            }
        }
        SpecExpression::Value(value) => {
            SpecExpression::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => SpecExpression::AlgebraicMatch {
            scrutinee: Box::new(substitute_bitvector_variable_in_spec_algebraic_expression(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| SpecAlgebraicMatchArm {
                    variant: arm.variant.clone(),
                    bindings: arm.bindings.clone(),
                    binding_types: arm.binding_types.clone(),
                    body: substitute_bitvector_variable_in_spec_expression(&arm.body, from, to),
                })
                .collect(),
        },
        SpecExpression::CExpression(expression) => SpecExpression::CExpression(
            substitute_bitvector_variable_in_c_expression(expression, from, to),
        ),
        SpecExpression::CountedResourceCount { name, arguments } => {
            SpecExpression::CountedResourceCount {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        argument.as_ref().map(|argument| {
                            substitute_bitvector_variable_in_spec_expression(argument, from, to)
                        })
                    })
                    .collect(),
            }
        }
        SpecExpression::Add(left, right) => SpecExpression::Add(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Subtract(left, right) => SpecExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Multiply(left, right) => SpecExpression::Multiply(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Divide(left, right) => SpecExpression::Divide(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::Remainder(left, right) => SpecExpression::Remainder(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::ShiftLeft(left, right) => SpecExpression::ShiftLeft(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::ShiftRight(left, right) => SpecExpression::ShiftRight(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseAnd(left, right) => SpecExpression::BitwiseAnd(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseOr(left, right) => SpecExpression::BitwiseOr(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseXor(left, right) => SpecExpression::BitwiseXor(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_expression(
                right, from, to,
            )),
        ),
        SpecExpression::BitwiseNot(expression) => SpecExpression::BitwiseNot(Box::new(
            substitute_bitvector_variable_in_spec_expression(expression, from, to),
        )),
        SpecExpression::Cast(expression, target_type) => SpecExpression::Cast(
            Box::new(substitute_bitvector_variable_in_spec_expression(
                expression, from, to,
            )),
            *target_type,
        ),
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => SpecExpression::If {
            condition: Box::new(substitute_bitvector_variable_in_spec_proposition(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_bitvector_variable_in_spec_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_bitvector_variable_in_spec_expression(
                else_branch,
                from,
                to,
            )),
        },
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => SpecExpression::RangeFold {
            start: Box::new(substitute_bitvector_variable_in_spec_expression(
                start, from, to,
            )),
            end: Box::new(substitute_bitvector_variable_in_spec_expression(
                end, from, to,
            )),
            initial: Box::new(substitute_bitvector_variable_in_spec_expression(
                initial, from, to,
            )),
            accumulator: accumulator.clone(),
            item: item.clone(),
            body: Box::new(substitute_bitvector_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::Let { name, value, body } => SpecExpression::Let {
            name: name.clone(),
            value: Box::new(substitute_bitvector_variable_in_spec_expression(
                value, from, to,
            )),
            body: Box::new(substitute_bitvector_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::PureFunctionApplication {
            name,
            arguments,
            result_type,
        } => SpecExpression::PureFunctionApplication {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_spec_function_argument(argument, from, to)
                })
                .collect(),
            result_type: *result_type,
        },
        SpecExpression::LoopEntrySnapshot(expression) => {
            SpecExpression::LoopEntrySnapshot(Box::new(
                substitute_bitvector_variable_in_spec_expression(expression, from, to),
            ))
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => SpecExpression::PointerOffset {
            pointer: Box::new(substitute_bitvector_variable_in_spec_expression(
                pointer, from, to,
            )),
            elements: Box::new(substitute_bitvector_variable_in_spec_expression(
                elements, from, to,
            )),
            byte_width: *byte_width,
        },
        SpecExpression::MemoryLoad {
            memory,
            pointer,
            value_type,
        } => SpecExpression::MemoryLoad {
            memory: substitute_bitvector_variable_in_spec_memory(memory, from, to),
            pointer: Box::new(substitute_bitvector_variable_in_spec_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
        },
    }
}

fn substitute_bitvector_variable_in_spec_function_argument(
    argument: &SpecPureFunctionArgument,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecPureFunctionArgument {
    match argument {
        SpecPureFunctionArgument::Integer(value) => SpecPureFunctionArgument::Integer(
            substitute_bitvector_variable_in_spec_integer(value, from, to),
        ),
        SpecPureFunctionArgument::Value(expression) => SpecPureFunctionArgument::Value(
            substitute_bitvector_variable_in_spec_expression(expression, from, to),
        ),
        SpecPureFunctionArgument::Algebraic(expression) => SpecPureFunctionArgument::Algebraic(
            substitute_bitvector_variable_in_spec_algebraic_expression(expression, from, to),
        ),
        SpecPureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => SpecPureFunctionArgument::ArrayRef {
            memory: substitute_bitvector_variable_in_spec_memory(memory, from, to),
            pointer: substitute_bitvector_variable_in_spec_expression(pointer, from, to),
            element_type: *element_type,
        },
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecProposition {
    match proposition {
        SpecProposition::IntegerComparison {
            left,
            operator,
            right,
        } => SpecProposition::IntegerComparison {
            left: substitute_bitvector_variable_in_spec_integer(left, from, to),
            operator: *operator,
            right: substitute_bitvector_variable_in_spec_integer(right, from, to),
        },
        SpecProposition::AlgebraicComparison { left, equal, right } => {
            SpecProposition::AlgebraicComparison {
                left: substitute_bitvector_variable_in_spec_algebraic_expression(left, from, to),
                equal: *equal,
                right: substitute_bitvector_variable_in_spec_algebraic_expression(right, from, to),
            }
        }
        SpecProposition::SequenceComparison { left, equal, right } => {
            SpecProposition::SequenceComparison {
                left: substitute_bitvector_variable_in_spec_sequence(left, from, to),
                equal: *equal,
                right: substitute_bitvector_variable_in_spec_sequence(right, from, to),
            }
        }
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => SpecProposition::Comparison {
            left: substitute_bitvector_variable_in_spec_expression(left, from, to),
            operator: *operator,
            right: substitute_bitvector_variable_in_spec_expression(right, from, to),
        },
        SpecProposition::And(left, right) => SpecProposition::And(
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Or(left, right) => SpecProposition::Or(
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Not(body) => SpecProposition::Not(Box::new(
            substitute_bitvector_variable_in_spec_proposition(body, from, to),
        )),
        SpecProposition::Implies(left, right) => SpecProposition::Implies(
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::ForAllInteger {
            name,
            variable,
            body,
        } if *variable != from => SpecProposition::ForAllInteger {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ForAllInt32 {
            name,
            variable,
            body,
        } if *variable != from => SpecProposition::ForAllInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ForAllPointer {
            name,
            variable,
            c_type,
            body,
        } if *variable != from => SpecProposition::ForAllPointer {
            name: name.clone(),
            variable: *variable,
            c_type: *c_type,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsInteger {
            name,
            variable,
            body,
        } if *variable != from => SpecProposition::ExistsInteger {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsInt32 {
            name,
            variable,
            body,
        } if *variable != from => SpecProposition::ExistsInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsPointer {
            name,
            variable,
            c_type,
            body,
        } if *variable != from => SpecProposition::ExistsPointer {
            name: name.clone(),
            variable: *variable,
            c_type: *c_type,
            body: Box::new(substitute_bitvector_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::Predicate { name, arguments } => SpecProposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| match argument {
                    SpecPredicateArgument::Value(expression) => SpecPredicateArgument::Value(
                        substitute_bitvector_variable_in_spec_expression(expression, from, to),
                    ),
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        SpecPredicateArgument::ArrayRef {
                            memory: memory.clone(),
                            pointer: substitute_bitvector_variable_in_spec_expression(
                                pointer, from, to,
                            ),
                        }
                    }
                })
                .collect(),
        },
        SpecProposition::ResourceSeparate { left, right } => SpecProposition::ResourceSeparate {
            left: substitute_bitvector_variable_in_spec_resource(left, from, to),
            right: substitute_bitvector_variable_in_spec_resource(right, from, to),
        },
        SpecProposition::ResourceContains { parent, child } => SpecProposition::ResourceContains {
            parent: substitute_bitvector_variable_in_spec_resource(parent, from, to),
            child: substitute_bitvector_variable_in_spec_resource(child, from, to),
        },
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            element_width,
        } => SpecProposition::MemoryLoadable {
            memory: substitute_bitvector_variable_in_spec_memory(memory, from, to),
            base: substitute_bitvector_variable_in_spec_expression(base, from, to),
            start: substitute_bitvector_variable_in_spec_expression(start, from, to),
            end: substitute_bitvector_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        proposition => proposition.clone(),
    }
}

fn substitute_bitvector_variable_in_spec_integer(
    expression: &SpecIntegerExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecIntegerExpression {
    match expression {
        SpecIntegerExpression::ResourceField(_) => expression.clone(),
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            SpecIntegerExpression::AlgebraicMatch {
                scrutinee: Box::new(substitute_bitvector_variable_in_spec_algebraic_expression(
                    scrutinee, from, to,
                )),
                arms: arms
                    .iter()
                    .map(|arm| SpecIntegerMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        binding_variables: arm.binding_variables.clone(),
                        body: Box::new(substitute_bitvector_variable_in_spec_integer(
                            &arm.body, from, to,
                        )),
                    })
                    .collect(),
            }
        }
        SpecIntegerExpression::PureFunctionApplication { name, arguments } => {
            SpecIntegerExpression::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_bitvector_variable_in_spec_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        SpecIntegerExpression::Term(term) => {
            SpecIntegerExpression::Term(substitute_bitvector_variable_in_integer(term, from, to))
        }
        SpecIntegerExpression::FromMachine(machine) => {
            SpecIntegerExpression::FromMachine(Box::new(
                substitute_bitvector_variable_in_spec_expression(machine, from, to),
            ))
        }
        SpecIntegerExpression::Negate(inner) => SpecIntegerExpression::Negate(Box::new(
            substitute_bitvector_variable_in_spec_integer(inner, from, to),
        )),
        SpecIntegerExpression::Add(left, right) => SpecIntegerExpression::Add(
            Box::new(substitute_bitvector_variable_in_spec_integer(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_integer(
                right, from, to,
            )),
        ),
        SpecIntegerExpression::Subtract(left, right) => SpecIntegerExpression::Subtract(
            Box::new(substitute_bitvector_variable_in_spec_integer(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_integer(
                right, from, to,
            )),
        ),
        SpecIntegerExpression::Multiply(left, right) => SpecIntegerExpression::Multiply(
            Box::new(substitute_bitvector_variable_in_spec_integer(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_integer(
                right, from, to,
            )),
        ),
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let index = match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                    SpecIntegerRangeFoldIndex::Int32 {
                        start: Box::new(substitute_bitvector_variable_in_spec_expression(
                            start, from, to,
                        )),
                        end: Box::new(substitute_bitvector_variable_in_spec_expression(
                            end, from, to,
                        )),
                    }
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    SpecIntegerRangeFoldIndex::Integer {
                        start: Box::new(substitute_bitvector_variable_in_spec_integer(
                            start, from, to,
                        )),
                        end: Box::new(substitute_bitvector_variable_in_spec_integer(end, from, to)),
                    }
                }
            };
            SpecIntegerExpression::RangeFold {
                index,
                initial: Box::new(substitute_bitvector_variable_in_spec_integer(
                    initial, from, to,
                )),
                accumulator: *accumulator,
                item: *item,
                body: Box::new(substitute_bitvector_variable_in_spec_integer(
                    body, from, to,
                )),
            }
        }
    }
}

#[cfg(test)]
mod machine_integer_substitution_tests {
    use super::*;

    #[test]
    fn machine_backed_integer_substitution_scales_with_shared_dag() {
        for depth in [8, 16, 32, 64] {
            let source = crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(7)),
            );
            let mut term = IntegerTerm::Machine(source);
            for _ in 0..depth {
                term = IntegerTerm::add(term.clone(), term.clone());
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &term,
                    Variable(7),
                    &Bitvector32Term::Constant(7),
                )
            });
            assert!(
                work <= (depth + 1) * 32,
                "unexpected shared DAG work at depth {depth}: {work}"
            );
        }
    }
}

fn substitute_bitvector_variable_in_spec_sequence(
    sequence: &SpecSequenceExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecSequenceExpression {
    match sequence {
        SpecSequenceExpression::Literal(elements) => SpecSequenceExpression::Literal(
            elements
                .iter()
                .map(|element| substitute_bitvector_variable_in_spec_expression(element, from, to))
                .collect(),
        ),
        SpecSequenceExpression::Concat(left, right) => SpecSequenceExpression::Concat(
            Box::new(substitute_bitvector_variable_in_spec_sequence(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_spec_sequence(
                right, from, to,
            )),
        ),
    }
}

fn substitute_bitvector_variable_in_spec_resource(
    resource: &SpecResource,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecResource {
    match resource {
        SpecResource::Memory {
            base,
            start,
            end,
            element_width,
        } => SpecResource::Memory {
            base: substitute_bitvector_variable_in_spec_expression(base, from, to),
            start: substitute_bitvector_variable_in_spec_expression(start, from, to),
            end: substitute_bitvector_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        SpecResource::Composite { name, arguments } => SpecResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_spec_expression(argument, from, to)
                })
                .collect(),
        },
        SpecResource::Token { name, arguments } => SpecResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_spec_expression(argument, from, to)
                })
                .collect(),
        },
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_loop_effect(
    effect: &CLoopEffect,
    from: Variable,
    to: &Bitvector32Term,
) -> CLoopEffect {
    match effect {
        CLoopEffect::Immutable => CLoopEffect::Immutable,
        CLoopEffect::Mutable(segments) => CLoopEffect::Mutable(
            segments
                .iter()
                .map(|segment| CMemorySegment {
                    base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
                    start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
                    end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
                    element_width: segment.element_width,
                    guard: segment.guard.as_ref().map(|guard| {
                        substitute_bitvector_variable_in_spec_proposition(guard, from, to)
                    }),
                })
                .collect(),
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_expression_outcome(
    outcome: &CExpressionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CExpressionOutcome {
    match outcome {
        CExpressionOutcome::Value(value) => {
            CExpressionOutcome::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
        CExpressionOutcome::UndefinedBehavior(kind) => {
            CExpressionOutcome::UndefinedBehavior(kind.clone())
        }
        CExpressionOutcome::RuntimeError(kind) => CExpressionOutcome::RuntimeError(kind.clone()),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_statement_outcome(
    outcome: &CStatementOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CStatementOutcome {
    match outcome {
        CStatementOutcome::Normal(state) => {
            CStatementOutcome::Normal(substitute_bitvector_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Break(state) => {
            CStatementOutcome::Break(substitute_bitvector_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Continue(state) => {
            CStatementOutcome::Continue(substitute_bitvector_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Return { value, state } => CStatementOutcome::Return {
            value: substitute_bitvector_variable_in_c_value(value, from, to),
            state: substitute_bitvector_variable_in_c_state(state, from, to),
        },
        CStatementOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
        CStatementOutcome::UndefinedBehavior(kind) => {
            CStatementOutcome::UndefinedBehavior(kind.clone())
        }
        CStatementOutcome::RuntimeError(kind) => CStatementOutcome::RuntimeError(kind.clone()),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_function_outcome(
    outcome: &CFunctionOutcome,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunctionOutcome {
    match outcome {
        CFunctionOutcome::Return { value, state } => CFunctionOutcome::Return {
            value: substitute_bitvector_variable_in_c_value(value, from, to),
            state: substitute_bitvector_variable_in_c_state(state, from, to),
        },
        CFunctionOutcome::VerificationDiverges => CFunctionOutcome::VerificationDiverges,
        CFunctionOutcome::UndefinedBehavior(kind) => {
            CFunctionOutcome::UndefinedBehavior(kind.clone())
        }
        CFunctionOutcome::RuntimeError(kind) => CFunctionOutcome::RuntimeError(kind.clone()),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_state(
    state: &CState,
    from: Variable,
    to: &Bitvector32Term,
) -> CState {
    let bindings = std::sync::Arc::new(
        state
            .locals
            .bindings
            .iter()
            .map(|(name, binding)| {
                let binding = match binding {
                    CLocalBinding::Object {
                        value,
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::Object {
                        value: substitute_bitvector_variable_in_c_value(value, from, to),
                        c_type: *c_type,
                        slot: slot.clone(),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::UninitializedObject {
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::UninitializedObject {
                        c_type: *c_type,
                        slot: slot.clone(),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::GlobalObject {
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::GlobalObject {
                        c_type: *c_type,
                        slot: slot.clone(),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::ArrayObject {
                        element_type,
                        length,
                        slot,
                        constant,
                    } => CLocalBinding::ArrayObject {
                        element_type: *element_type,
                        length: *length,
                        slot: slot.clone(),
                        constant: *constant,
                    },
                    CLocalBinding::AggregateObject {
                        layout,
                        slot,
                        constant,
                    } => CLocalBinding::AggregateObject {
                        layout: layout.clone(),
                        slot: slot.clone(),
                        constant: *constant,
                    },
                };
                (name.clone(), binding)
            })
            .collect(),
    );
    CState {
        locals: CLocalEnvironment {
            bindings,
            slots: state.locals.slots.clone(),
        },
        memory: substitute_bitvector_variable_in_memory(&state.memory, from, to),
        resource_bindings: state.resource_bindings.clone(),
        instance_field_scope: substitute_bitvector_variable_in_resource_context(
            &state.instance_field_scope,
            from,
            to,
        ),
        resources: substitute_bitvector_variable_in_resource_context(&state.resources, from, to),
        next_local_frame: state.next_local_frame,
        next_local_lifetime: state.next_local_lifetime,
        counted_populations: std::sync::Arc::new(
            state
                .counted_populations
                .iter()
                .map(|population| CCountedPopulation {
                    name: population.name.clone(),
                    arguments: population
                        .arguments
                        .iter()
                        .map(|argument| {
                            substitute_bitvector_variable_in_algebraic_value(argument, from, to)
                        })
                        .collect(),
                    count: match substitute_bitvector_variable_in_c_value(
                        &CValue::Int32(population.count.clone()),
                        from,
                        to,
                    ) {
                        CValue::Int32(count) => count,
                        _ => unreachable!("an int32 population count remains int32"),
                    },
                    family_observation_marker: population.family_observation_marker,
                })
                .collect(),
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_resource_context(
    resources: &ResourceContext,
    from: Variable,
    to: &Bitvector32Term,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_facts(
        resources
            .facts()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource(resource, from, to)),
    )
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_resource(
    resource: &CResourceFact,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceFact {
    match resource {
        CResourceFact::Own(resource, quantity) => CResourceFact::Own(
            substitute_bitvector_variable_in_c_resource(resource, from, to),
            Box::new(substitute_bitvector_variable(quantity, from, to)),
        ),
        CResourceFact::View(resource) => CResourceFact::View(
            substitute_bitvector_variable_in_c_resource(resource, from, to),
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_resource(
    resource: &CResource,
    from: Variable,
    to: &Bitvector32Term,
) -> CResource {
    match resource {
        CResource::Instance(instance) => {
            let mut result = instance.clone();
            result.arguments = instance
                .arguments
                .iter()
                .map(|value| substitute_bitvector_variable_in_algebraic_value(value, from, to))
                .collect();
            result.fields = instance
                .fields
                .iter()
                .map(|value| substitute_bitvector_variable_in_algebraic_value(value, from, to))
                .collect();
            CResource::Instance(result)
        }
        CResource::Memory(range) => CResource::Memory(
            substitute_bitvector_variable_in_c_memory_range(range, from, to),
        ),
        CResource::Composite { name, arguments } => CResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_algebraic_value(argument, from, to)
                })
                .collect(),
        },
        CResource::Token { name, arguments } => CResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_bitvector_variable_in_algebraic_value(argument, from, to)
                })
                .collect(),
        },
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_function(
    function: &CFunction,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunction {
    let mut interface = function.contract_interface().clone();
    interface.resource_requires = function
        .resource_requires()
        .iter()
        .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
        .collect();
    interface.resource_ensures = function
        .resource_ensures()
        .iter()
        .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
        .collect();
    interface.resource_constructors = function
        .resource_constructors()
        .iter()
        .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
        .collect();
    interface.contract_requires = function
        .contract_requires()
        .iter()
        .map(|proposition| substitute_bitvector_variable_in_spec_proposition(proposition, from, to))
        .collect();
    interface.contract_ensures = function
        .contract_ensures()
        .iter()
        .map(|proposition| substitute_bitvector_variable_in_spec_proposition(proposition, from, to))
        .collect();
    interface.contract_mutable = function
        .contract_mutable()
        .iter()
        .map(|segment| substitute_bitvector_variable_in_c_memory_segment(segment, from, to))
        .collect();
    interface.resource_derived_mutable_segments = function
        .contract_interface()
        .resource_derived_mutable_segments
        .iter()
        .map(|segment| substitute_bitvector_variable_in_c_memory_segment(segment, from, to))
        .collect();
    interface.composite_resource_definitions = function
        .composite_resource_definitions()
        .iter()
        .map(|definition| CCompositeResourceDefinition {
            instance_schema: definition.instance_schema.clone(),
            name: definition.name.clone(),
            parameters: definition.parameters.clone(),
            witnesses: definition.witnesses.clone(),
            condition: definition.condition.as_ref().map(|condition| {
                substitute_bitvector_variable_in_spec_proposition(condition, from, to)
            }),
            matched: definition.matched.as_ref().map(|body| CResourceMatchBody {
                field_index: body.field_index,
                algebraic_type: body.algebraic_type.clone(),
                arms: body
                    .arms
                    .iter()
                    .map(|arm| CResourceMatchArm {
                        children: arm
                            .children
                            .iter()
                            .map(|child| CResourceChildSpec {
                                name: child.name.clone(),
                                resource: child.resource.clone(),
                                binding: child.binding,
                                field_bindings: child.field_bindings.clone(),
                                arguments: child
                                    .arguments
                                    .iter()
                                    .map(|argument| {
                                        substitute_bitvector_variable_in_c_expression(
                                            argument, from, to,
                                        )
                                    })
                                    .collect(),
                            })
                            .collect(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        binding_variables: arm.binding_variables.clone(),
                        contains: arm
                            .contains
                            .iter()
                            .map(|resource| {
                                substitute_bitvector_variable_in_resource_spec(resource, from, to)
                            })
                            .collect(),
                        facts: arm
                            .facts
                            .iter()
                            .map(|fact| {
                                substitute_bitvector_variable_in_spec_proposition(fact, from, to)
                            })
                            .collect(),
                    })
                    .collect(),
            }),
            recursive: definition.recursive,
            matched_recursive: definition.matched_recursive,
            counted_population: definition.counted_population,
            contains: definition
                .contains
                .iter()
                .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
                .collect(),
            facts: definition
                .facts
                .iter()
                .map(|fact| substitute_bitvector_variable_in_spec_proposition(fact, from, to))
                .collect(),
        })
        .collect();
    interface.predicate_unfoldings = function
        .predicate_unfoldings()
        .iter()
        .map(|unfolding| CPredicateUnfolding {
            predicate: substitute_bitvector_variable_in_spec_proposition(
                &unfolding.predicate,
                from,
                to,
            ),
            body: substitute_bitvector_variable_in_spec_proposition(&unfolding.body, from, to),
        })
        .collect();
    CFunction {
        program_entry: function.program_entry,
        name: function.name.clone(),
        inline_body: function.inline_body,
        body: substitute_bitvector_variable_in_c_statement(function.body(), from, to),
        source_body: substitute_bitvector_variable_in_c_statement(function.source_body(), from, to),
        contract_interface: interface,
        global_variables: function.global_variables.clone(),
        global_arrays: function.global_arrays.clone(),
        static_variables: function.static_variables.clone(),
        static_storage: function.static_storage.clone(),
        string_literals: function.string_literals.clone(),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_resource_spec(
    resource: &CResourceSpec,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceSpec {
    CResourceSpec::new(
        substitute_bitvector_variable_in_resource_term(resource.term(), from, to),
        resource.access(),
        match resource.quantity() {
            CResourceQuantity::One => CResourceQuantity::One,
            CResourceQuantity::Count(quantity) => CResourceQuantity::Count(
                substitute_bitvector_variable_in_c_expression(quantity, from, to),
            ),
        },
        resource.role(),
        resource.snapshot(),
    )
    .expect("bitvector substitution preserves resource validity")
}

fn substitute_bitvector_variable_in_resource_term(
    resource: &CResourceTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceTerm {
    match resource {
        CResourceTerm::Instance {
            identity,
            binder,
            schema,
            resource,
        } => CResourceTerm::Instance {
            identity: *identity,
            binder: binder.clone(),
            schema: schema.clone(),
            resource: Box::new(substitute_bitvector_variable_in_resource_term(
                resource, from, to,
            )),
        },
        CResourceTerm::Memory(segment) => CResourceTerm::Memory(CMemorySegment {
            base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
            start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
            end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
            element_width: segment.element_width,
            guard: segment
                .guard
                .as_ref()
                .map(|guard| substitute_bitvector_variable_in_spec_proposition(guard, from, to)),
        }),
        CResourceTerm::Composite {
            name,
            arguments,
            parameter_types,
        } => CResourceTerm::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
        CResourceTerm::Token {
            name,
            arguments,
            parameter_types,
        } => CResourceTerm::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_function_specification(
    specification: &CFunctionSpecification,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunctionSpecification {
    CFunctionSpecification {
        state: substitute_bitvector_variable_in_c_state(specification.state(), from, to),
        arguments: specification
            .arguments()
            .iter()
            .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
            .collect(),
        requires: specification
            .requires()
            .iter()
            .map(|requirement| substitute_bitvector_variable_in_proposition(requirement, from, to))
            .collect(),
        outcome: substitute_bitvector_variable_in_c_function_outcome(
            specification.outcome(),
            from,
            to,
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_memory_range(
    range: &CMemoryRange,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemoryRange {
    range.with_bounds(
        substitute_bitvector_variable_in_pointer(&range.base, from, to),
        substitute_bitvector_variable(&range.start, from, to),
        substitute_bitvector_variable(&range.end, from, to),
    )
}

fn substitute_bitvector_variable_in_c_memory_segment(
    segment: &CMemorySegment,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemorySegment {
    CMemorySegment {
        base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
        start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
        end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
        element_width: segment.element_width,
        guard: segment
            .guard
            .as_ref()
            .map(|guard| substitute_bitvector_variable_in_spec_proposition(guard, from, to)),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> ConditionTerm {
    match condition {
        ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
        ConditionTerm::AlgebraicEqual(left, right) => ConditionTerm::AlgebraicEqual(
            Box::new(substitute_bitvector_variable_in_algebraic_term(
                left, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_algebraic_term(
                right, from, to,
            )),
        ),
        ConditionTerm::Variable(variable) => ConditionTerm::Variable(*variable),
        ConditionTerm::Bitvector32SignedLessThan(left, right) => ConditionTerm::signed_less_than(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => ConditionTerm::signed_less_equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            ConditionTerm::signed_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            ConditionTerm::signed_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32Equal(left, right) => ConditionTerm::equal(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            ConditionTerm::signed_add_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            ConditionTerm::signed_subtract_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            ConditionTerm::signed_multiply_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            ConditionTerm::signed_divide_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            ConditionTerm::signed_shift_left_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedLessThan(left, right) => {
            ConditionTerm::int64_signed_less_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
            ConditionTerm::int64_signed_less_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
            ConditionTerm::int64_signed_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
            ConditionTerm::int64_signed_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64UnsignedLessThan(left, right) => ConditionTerm::uint64_less_than(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            ConditionTerm::uint64_less_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            ConditionTerm::uint64_greater_than(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            ConditionTerm::uint64_greater_equal(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64Equal(left, right) => ConditionTerm::Bitvector64Equal(
            Box::new(substitute_bitvector_variable(left, from, to)),
            Box::new(substitute_bitvector_variable(right, from, to)),
        ),
        ConditionTerm::Bitvector64SignedAddOverflows(left, right) => {
            ConditionTerm::int64_signed_add_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedSubtractOverflows(left, right) => {
            ConditionTerm::int64_signed_subtract_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right) => {
            ConditionTerm::int64_signed_multiply_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedDivideOverflows(left, right) => {
            ConditionTerm::int64_signed_divide_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            ConditionTerm::int64_signed_shift_left_overflows(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            let rewrite =
                |term: &IntegerTerm| substitute_bitvector_variable_in_integer(term, from, to);
            match condition {
                ConditionTerm::IntegerLessThan(_, _) => {
                    ConditionTerm::integer_less_than(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerLessEqual(_, _) => {
                    ConditionTerm::integer_less_equal(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerGreaterThan(_, _) => {
                    ConditionTerm::integer_greater_than(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerGreaterEqual(_, _) => {
                    ConditionTerm::integer_greater_equal(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerEqual(_, _) => {
                    ConditionTerm::integer_equal(rewrite(left), rewrite(right))
                }
                ConditionTerm::IntegerNotEqual(_, _) => {
                    ConditionTerm::integer_not_equal(rewrite(left), rewrite(right))
                }
                _ => unreachable!(),
            }
        }
        ConditionTerm::Float32(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => ConditionTerm::float32_compare(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        ConditionTerm::Float32(CFloatCondition::Classification {
            classification,
            value,
        }) => ConditionTerm::float32_classification(
            substitute_bitvector_variable(value, from, to),
            *classification,
        ),
        ConditionTerm::Float64(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => ConditionTerm::float64_compare(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        ConditionTerm::Float64(CFloatCondition::Classification {
            classification,
            value,
        }) => ConditionTerm::float64_classification(
            substitute_bitvector_variable(value, from, to),
            *classification,
        ),
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::pointer_offset_equal(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            substitute_bitvector_variable_in_pointer(left, from, to),
            substitute_bitvector_variable_in_pointer(right, from, to),
        ),
    }
}

fn substitute_through_load_variable(
    variable: Variable,
    from: Variable,
    to: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    if !crate::kernel::is_load_variable(&variable) {
        return None;
    }
    let (memory, pointer) = crate::kernel::eval::registered_load_for_variable(&variable)?;
    let substituted_pointer = Pointer {
        block: pointer.block.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    };
    let substituted_memory = substitute_bitvector_variable_in_memory(&memory, from, to);
    if substituted_pointer == pointer && substituted_memory == *memory {
        return None;
    }
    Some(crate::kernel::eval::canonical_term(
        &Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(substituted_memory),
            Box::new(substituted_pointer),
        ),
    ))
}

pub(crate) fn substitute_bitvector_variable(
    term: &Bitvector32Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
        Bitvector32Term::Int64Constant(value) => Bitvector32Term::Int64Constant(*value),
        Bitvector32Term::UInt64Constant(value) => Bitvector32Term::UInt64Constant(*value),
        Bitvector32Term::Variable(variable) if *variable == from => to.clone(),
        Bitvector32Term::Variable(variable) => {
            // A load variable can represent a load whose address mentions
            // the substituted variable (a universal's body contains `p[k]`
            // with the bound `k` inside the address). Substitution reaches
            // through the variable into the load and takes the canonical
            // form of the result, so instantiating a universal yields the
            // same load variable as a direct read of that cell.
            substitute_through_load_variable(*variable, from, to)
                .unwrap_or(Bitvector32Term::Variable(*variable))
        }
        Bitvector32Term::Int64From32(value) => {
            Bitvector32Term::int64_from_32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64From32(value) => {
            Bitvector32Term::uint64_from_32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt32From64(value) => {
            Bitvector32Term::uint32_from_64(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Int64FromUInt32(value) => {
            Bitvector32Term::int64_from_uint32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64FromInt32(value) => {
            Bitvector32Term::uint64_from_int32(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64FromInt64(value) => {
            Bitvector32Term::uint64_from_int64(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Int64Add(left, right) => Bitvector32Term::int64_add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Subtract(left, right) => Bitvector32Term::int64_subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Multiply(left, right) => Bitvector32Term::int64_multiply(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Divide(left, right) => Bitvector32Term::int64_divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64Remainder(left, right) => Bitvector32Term::int64_remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64ShiftLeft(left, right) => Bitvector32Term::int64_shift_left(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64ArithmeticShiftRight(left, right) => {
            Bitvector32Term::int64_arithmetic_shift_right(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        Bitvector32Term::Int64BitwiseAnd(left, right) => Bitvector32Term::int64_bitwise_and(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64BitwiseOr(left, right) => Bitvector32Term::int64_bitwise_or(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64BitwiseXor(left, right) => Bitvector32Term::int64_bitwise_xor(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Int64BitwiseNot(value) => {
            Bitvector32Term::int64_bitwise_not(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::UInt64Add(left, right) => Bitvector32Term::uint64_add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Subtract(left, right) => Bitvector32Term::uint64_subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Multiply(left, right) => Bitvector32Term::uint64_multiply(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Divide(left, right) => Bitvector32Term::uint64_divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64Remainder(left, right) => Bitvector32Term::uint64_remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64ShiftLeft(left, right) => Bitvector32Term::uint64_shift_left(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            Bitvector32Term::uint64_logical_shift_right(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        Bitvector32Term::UInt64BitwiseAnd(left, right) => Bitvector32Term::uint64_bitwise_and(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64BitwiseOr(left, right) => Bitvector32Term::uint64_bitwise_or(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64BitwiseXor(left, right) => Bitvector32Term::uint64_bitwise_xor(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UInt64BitwiseNot(value) => {
            Bitvector32Term::uint64_bitwise_not(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Float32Negate(value) => {
            Bitvector32Term::float32_negate(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Float32Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::float32_binary(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        Bitvector32Term::Float64Negate(value) => {
            Bitvector32Term::float64_negate(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::Float64Binary {
            operator,
            left,
            right,
        } => Bitvector32Term::float64_binary(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
            *operator,
        ),
        Bitvector32Term::Add(left, right) => Bitvector32Term::add(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::subtract(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::multiply(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Divide(left, right) => Bitvector32Term::divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UnsignedDivide(left, right) => Bitvector32Term::unsigned_divide(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::Remainder(left, right) => Bitvector32Term::remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::UnsignedRemainder(left, right) => Bitvector32Term::unsigned_remainder(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::ShiftLeft(left, right) => Bitvector32Term::shift_left(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            Bitvector32Term::arithmetic_shift_right(
                substitute_bitvector_variable(left, from, to),
                substitute_bitvector_variable(right, from, to),
            )
        }
        Bitvector32Term::LogicalShiftRight(left, right) => Bitvector32Term::logical_shift_right(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseAnd(left, right) => Bitvector32Term::bitwise_and(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseOr(left, right) => Bitvector32Term::bitwise_or(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseXor(left, right) => Bitvector32Term::bitwise_xor(
            substitute_bitvector_variable(left, from, to),
            substitute_bitvector_variable(right, from, to),
        ),
        Bitvector32Term::BitwiseNot(value) => {
            Bitvector32Term::bitwise_not(substitute_bitvector_variable(value, from, to))
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::if_then_else(
            substitute_bitvector_variable_in_condition(condition, from, to),
            substitute_bitvector_variable(then_term, from, to),
            substitute_bitvector_variable(else_term, from, to),
        ),
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut body = body.as_ref().clone();
            let original_accumulator = *accumulator;
            let original_item = *item;
            let mut accumulator = *accumulator;
            let mut item = *item;
            let mut replacement_variables = BTreeSet::new();
            collect_bitvector_variables(to, &mut replacement_variables);

            // A fold binder shadows `from` in the body, so no substitution
            // enters that body in this case. Otherwise rename a binder that
            // occurs in the replacement before descending into the body.
            // The fresh names are reserved against both free and nested fold
            // variables, so the two renames cannot collide with one another.
            if original_accumulator != from && replacement_variables.contains(&accumulator) {
                let mut reserved = BTreeSet::new();
                collect_bitvector_variables(&body, &mut reserved);
                collect_bitvector_bound_variables(&body, &mut reserved);
                reserved.extend(replacement_variables.iter().copied());
                reserved.insert(from);
                reserved.insert(accumulator);
                reserved.insert(item);
                let mut fresh = KernelVariableGenerator::fresh_for(0, reserved);
                let renamed = fresh.next();
                body = substitute_bitvector_variable(
                    &body,
                    accumulator,
                    &Bitvector32Term::Variable(renamed),
                );
                accumulator = renamed;
            }
            if original_item != from && replacement_variables.contains(&item) {
                let mut reserved = BTreeSet::new();
                collect_bitvector_variables(&body, &mut reserved);
                collect_bitvector_bound_variables(&body, &mut reserved);
                reserved.extend(replacement_variables.iter().copied());
                reserved.insert(from);
                reserved.insert(accumulator);
                reserved.insert(item);
                let mut fresh = KernelVariableGenerator::fresh_for(0, reserved);
                let renamed = fresh.next();
                body =
                    substitute_bitvector_variable(&body, item, &Bitvector32Term::Variable(renamed));
                item = renamed;
            }
            if original_accumulator != from && original_item != from {
                body = substitute_bitvector_variable(&body, from, to);
            }
            Bitvector32Term::range_fold(
                substitute_bitvector_variable(start, from, to),
                substitute_bitvector_variable(end, from, to),
                substitute_bitvector_variable(initial, from, to),
                accumulator,
                item,
                body,
            )
        }
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| substitute_bitvector_variable(argument, from, to))
                    .collect(),
            }
        }
        Bitvector32Term::ClickFunctionApplication { name, arguments } => {
            Bitvector32Term::ClickFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_bitvector_variable_in_pure_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => Bitvector32Term::AlgebraicMatch {
            scrutinee: Box::new(substitute_bitvector_variable_in_algebraic_term(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| AlgebraicBitvectorMatchArm {
                    variant: arm.variant.clone(),
                    bindings: arm
                        .bindings
                        .iter()
                        .map(|binding| {
                            substitute_bitvector_variable_in_algebraic_value(binding, from, to)
                        })
                        .collect(),
                    body: substitute_bitvector_variable(&arm.body, from, to),
                })
                .collect(),
        },
        Bitvector32Term::MemoryLoad(memory, pointer) => Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(substitute_bitvector_variable_in_memory(
                memory, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_pointer(pointer, from, to)),
        ),
        Bitvector32Term::PointerAddress(pointer) => Bitvector32Term::PointerAddress(Box::new(
            substitute_bitvector_variable_in_pointer(pointer, from, to),
        )),
        Bitvector32Term::IntegerToMachine { value, destination } => {
            Bitvector32Term::IntegerToMachine {
                value: substitute_bitvector_variable_in_integer(value.as_ref(), from, to).into(),
                destination: *destination,
            }
        }
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_pointer_offset(
    offset: &PointerOffsetTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> PointerOffsetTerm {
    match offset {
        PointerOffsetTerm::Constant(value) => PointerOffsetTerm::Constant(*value),
        PointerOffsetTerm::Variable(variable) => PointerOffsetTerm::Variable(*variable),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            substitute_bitvector_variable_in_pointer_offset(left, from, to),
            substitute_bitvector_variable_in_pointer_offset(right, from, to),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            substitute_bitvector_variable(value, from, to),
            *byte_width,
        ),
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => PointerOffsetTerm::scale_int64(
            substitute_bitvector_variable(value, from, to),
            *byte_width,
            *unsigned,
        ),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_pointer(
    pointer: &Pointer,
    from: Variable,
    to: &Bitvector32Term,
) -> Pointer {
    Pointer {
        block: pointer.block.clone(),
        offset: substitute_bitvector_variable_in_pointer_offset(&pointer.offset, from, to),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_memory(
    memory: &CMemory,
    from: Variable,
    to: &Bitvector32Term,
) -> CMemory {
    let cells = std::sync::Arc::new(
        memory
            .cells
            .iter()
            .map(|(pointer, value)| {
                (
                    substitute_bitvector_variable_in_pointer(pointer, from, to),
                    substitute_bitvector_variable_in_c_value(value, from, to),
                )
            })
            .collect(),
    );
    CMemory {
        blocks: std::sync::Arc::new(
            memory
                .blocks
                .iter()
                .map(|(block, contents)| {
                    (
                        block.clone(),
                        CBlock::with_symbolic_size(substitute_bitvector_variable(
                            contents.size(),
                            from,
                            to,
                        )),
                    )
                })
                .collect(),
        ),
        cells,
        union_cells: std::sync::Arc::new(
            memory
                .union_cells
                .iter()
                .map(|((pointer, c_type), value)| {
                    (
                        (
                            substitute_bitvector_variable_in_pointer(pointer, from, to),
                            *c_type,
                        ),
                        substitute_bitvector_variable_in_c_value(value, from, to),
                    )
                })
                .collect(),
        ),
        ended_local_blocks: memory.ended_local_blocks.clone(),
        heap: std::sync::Arc::new(CHeapMemory {
            live_allocations: memory
                .heap
                .live_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        substitute_bitvector_variable(bytes, from, to),
                    )
                })
                .collect(),
            deallocated_allocations: memory
                .heap
                .deallocated_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        substitute_bitvector_variable(bytes, from, to),
                    )
                })
                .collect(),
            pending_allocations: memory
                .heap
                .pending_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        substitute_bitvector_variable(bytes, from, to),
                    )
                })
                .collect(),
            uninitialized_allocations: memory
                .heap
                .uninitialized_allocations
                .iter()
                .map(|base| substitute_bitvector_variable_in_pointer(base, from, to))
                .collect(),
            zeroed_allocations: memory
                .heap
                .zeroed_allocations
                .iter()
                .map(|base| substitute_bitvector_variable_in_pointer(base, from, to))
                .collect(),
            zeroed_prefix_allocations: memory
                .heap
                .zeroed_prefix_allocations
                .iter()
                .map(|(base, prefix)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        substitute_bitvector_variable(prefix, from, to),
                    )
                })
                .collect(),
            zeroed_pending_allocations: memory
                .heap
                .zeroed_pending_allocations
                .iter()
                .map(|base| substitute_bitvector_variable_in_pointer(base, from, to))
                .collect(),
            pending_reallocations: memory
                .heap
                .pending_reallocations
                .iter()
                .map(|(base, pending)| {
                    (
                        substitute_bitvector_variable_in_pointer(base, from, to),
                        CPendingReallocation {
                            old_pointer: substitute_bitvector_variable_in_pointer(
                                &pending.old_pointer,
                                from,
                                to,
                            ),
                            old_bytes: substitute_bitvector_variable(&pending.old_bytes, from, to),
                            zeroed_prefix: pending
                                .zeroed_prefix
                                .as_ref()
                                .map(|prefix| substitute_bitvector_variable(prefix, from, to)),
                            copied_cells: pending
                                .copied_cells
                                .iter()
                                .map(|(offset, value)| {
                                    (
                                        substitute_bitvector_variable_in_pointer_offset(
                                            offset, from, to,
                                        ),
                                        substitute_bitvector_variable_in_c_value(value, from, to),
                                    )
                                })
                                .collect(),
                        },
                    )
                })
                .collect(),
        }),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_value(
    value: &CValue,
    from: Variable,
    to: &Bitvector32Term,
) -> CValue {
    match value {
        CValue::Void => CValue::Void,
        CValue::Bool(bits) => CValue::Bool(substitute_bitvector_variable(bits, from, to)),
        CValue::Int16(bits) => int16(substitute_bitvector_variable(bits, from, to)),
        CValue::Int32(bits) => int32(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt8(bits) => uint8(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt16(bits) => uint16(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt32(bits) => uint32(substitute_bitvector_variable(bits, from, to)),
        CValue::Int64(bits) => CValue::Int64(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt64(bits) => CValue::UInt64(substitute_bitvector_variable(bits, from, to)),
        CValue::Float32(bits) => CValue::Float32(substitute_bitvector_variable(bits, from, to)),
        CValue::Float64(bits) => CValue::Float64(substitute_bitvector_variable(bits, from, to)),
        CValue::Pointer(pointer) => CValue::typed_pointer(
            substitute_bitvector_variable_in_pointer(pointer.pointer(), from, to),
            pointer.c_type(),
        )
        .with_pointer_pointee_volatile(pointer.pointee_volatile())
        .with_pointer_pointee_constant(pointer.pointee_constant()),
    }
}

/// Substitute a complete pointer value for a quantified pointer variable.
///
/// Pointer variables are represented by symbolic block identities rather
/// than by integer addresses.  Substitution therefore replaces the symbolic
/// block and composes the replacement's offset with any pointer arithmetic
/// already present at the occurrence.  In particular, substituting `q` for
/// `p` in `p + 4` must produce `q + 4`, not merely `q`.
pub(crate) fn substitute_pointer_variable_in_proposition(
    proposition: &Proposition,
    from: Variable,
    to: &Pointer,
) -> Proposition {
    match proposition {
        Proposition::Equal(left, right) => Proposition::Equal(
            substitute_pointer_variable_in_term(left, from, to),
            substitute_pointer_variable_in_term(right, from, to),
        ),
        Proposition::ConditionIs(condition, value) => Proposition::ConditionIs(
            substitute_pointer_variable_in_condition(condition, from, to),
            *value,
        ),
        Proposition::Predicate { name, arguments } => Proposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_term(argument, from, to))
                .collect(),
        },
        Proposition::CExpressionEvaluates {
            state,
            expression,
            outcome,
        } => Proposition::CExpressionEvaluates {
            state: substitute_pointer_variable_in_c_state(state, from, to),
            expression: substitute_pointer_variable_in_c_expression(expression, from, to),
            outcome: substitute_pointer_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CConditionEvaluates {
            state,
            condition,
            outcome,
        } => Proposition::CConditionEvaluates {
            state: substitute_pointer_variable_in_c_state(state, from, to),
            condition: substitute_pointer_variable_in_c_expression(condition, from, to),
            outcome: outcome.clone(),
        },
        Proposition::CStatementExecutes {
            state,
            statement,
            outcome,
        }
        | Proposition::CStatementVerifies {
            state,
            statement,
            outcome,
        } => {
            let state = substitute_pointer_variable_in_c_state(state, from, to);
            let statement = substitute_pointer_variable_in_c_statement(statement, from, to);
            let outcome = substitute_pointer_variable_in_c_statement_outcome(outcome, from, to);
            match proposition {
                Proposition::CStatementExecutes { .. } => Proposition::CStatementExecutes {
                    state,
                    statement,
                    outcome,
                },
                Proposition::CStatementVerifies { .. } => Proposition::CStatementVerifies {
                    state,
                    statement,
                    outcome,
                },
                _ => unreachable!("the combined statement proposition arm is exhaustive"),
            }
        }
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
        } => {
            let state = substitute_pointer_variable_in_c_state(state, from, to);
            let function = substitute_pointer_variable_in_c_function(function, from, to);
            let arguments = arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_expression(argument, from, to))
                .collect();
            let outcome = substitute_pointer_variable_in_c_function_outcome(outcome, from, to);
            match proposition {
                Proposition::CFunctionExecutes { .. } => Proposition::CFunctionExecutes {
                    state,
                    function,
                    arguments,
                    outcome,
                },
                Proposition::CFunctionVerifies { .. } => Proposition::CFunctionVerifies {
                    state,
                    function,
                    arguments,
                    outcome,
                },
                _ => unreachable!("the combined function proposition arm is exhaustive"),
            }
        }
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionSatisfiesSpecification {
            function: substitute_pointer_variable_in_c_function(function, from, to),
            specification: substitute_pointer_variable_in_c_function_specification(
                specification,
                from,
                to,
            ),
        },
        Proposition::CFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => Proposition::CFunctionPartiallySatisfiesSpecification {
            function: substitute_pointer_variable_in_c_function(function, from, to),
            specification: substitute_pointer_variable_in_c_function_specification(
                specification,
                from,
                to,
            ),
        },
        Proposition::CMemoryLoads {
            memory,
            pointer,
            outcome,
        } => Proposition::CMemoryLoads {
            memory: substitute_pointer_variable_in_memory(memory, from, to),
            pointer: substitute_pointer_variable_in_pointer(pointer, from, to),
            outcome: substitute_pointer_variable_in_c_expression_outcome(outcome, from, to),
        },
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => Proposition::CMemoryCanStore {
            memory: substitute_pointer_variable_in_memory(memory, from, to),
            pointer: substitute_pointer_variable_in_pointer(pointer, from, to),
            byte_width: *byte_width,
        },
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => Proposition::CMemoryLoadable {
            memory: substitute_pointer_variable_in_memory(memory, from, to),
            base: substitute_pointer_variable_in_pointer(base, from, to),
            bytes: bytes.clone(),
        },
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => Proposition::CMemoryDisjoint {
            left_base: substitute_pointer_variable_in_pointer(left_base, from, to),
            left_start: left_start.clone(),
            left_end: left_end.clone(),
            right_base: substitute_pointer_variable_in_pointer(right_base, from, to),
            right_start: right_start.clone(),
            right_end: right_end.clone(),
        },
        Proposition::CResourceSeparate { left, right } => Proposition::CResourceSeparate {
            left: substitute_pointer_variable_in_c_resource(left, from, to),
            right: substitute_pointer_variable_in_c_resource(right, from, to),
        },
        Proposition::CResourceContains { parent, child } => Proposition::CResourceContains {
            parent: substitute_pointer_variable_in_c_resource(parent, from, to),
            child: substitute_pointer_variable_in_c_resource(child, from, to),
        },
        Proposition::CResourceComposition(resources) => Proposition::CResourceComposition(
            substitute_pointer_variable_in_resource_context(resources, from, to),
        ),
        Proposition::CMemoryMutatesOnly {
            before,
            after,
            pointers,
        } => Proposition::CMemoryMutatesOnly {
            before: substitute_pointer_variable_in_memory(before, from, to),
            after: substitute_pointer_variable_in_memory(after, from, to),
            pointers: pointers
                .iter()
                .map(|pointer| substitute_pointer_variable_in_pointer(pointer, from, to))
                .collect(),
        },
        Proposition::CMemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => Proposition::CMemoryEffectSummary {
            before: substitute_pointer_variable_in_memory(before, from, to),
            after: substitute_pointer_variable_in_memory(after, from, to),
            mutable_ranges: mutable_ranges
                .iter()
                .map(|range| substitute_pointer_variable_in_c_memory_range(range, from, to))
                .collect(),
        },
        Proposition::CHeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => Proposition::CHeapAllocationFreed {
            before: substitute_pointer_variable_in_memory(before, from, to),
            after: substitute_pointer_variable_in_memory(after, from, to),
            allocation_base: substitute_pointer_variable_in_pointer(allocation_base, from, to),
            bytes: bytes.clone(),
        },
        Proposition::And(left, right) => Proposition::And(
            Box::new(substitute_pointer_variable_in_proposition(left, from, to)),
            Box::new(substitute_pointer_variable_in_proposition(right, from, to)),
        ),
        Proposition::Or(left, right) => Proposition::Or(
            Box::new(substitute_pointer_variable_in_proposition(left, from, to)),
            Box::new(substitute_pointer_variable_in_proposition(right, from, to)),
        ),
        Proposition::Not(body) => Proposition::Not(Box::new(
            substitute_pointer_variable_in_proposition(body, from, to),
        )),
        Proposition::Implies(left, right) => Proposition::Implies(
            Box::new(substitute_pointer_variable_in_proposition(left, from, to)),
            Box::new(substitute_pointer_variable_in_proposition(right, from, to)),
        ),
        Proposition::ForAll { var, sort, body } if *var != from => {
            let (body, var) = pointer_capture_avoiding_quantifier_body(*var, sort, body, from, to);
            Proposition::ForAll {
                var,
                sort: sort.clone(),
                body: Box::new(substitute_pointer_variable_in_proposition(&body, from, to)),
            }
        }
        Proposition::Exists {
            name,
            var,
            sort,
            body,
        } if *var != from => {
            let (body, var) = pointer_capture_avoiding_quantifier_body(*var, sort, body, from, to);
            Proposition::Exists {
                name: name.clone(),
                var,
                sort: sort.clone(),
                body: Box::new(substitute_pointer_variable_in_proposition(&body, from, to)),
            }
        }
        proposition => proposition.clone(),
    }
}

fn pointer_capture_avoiding_quantifier_body(
    binder: Variable,
    sort: &Sort,
    body: &Proposition,
    from: Variable,
    replacement: &Pointer,
) -> (Proposition, Variable) {
    let replacement_variable = match replacement.block {
        PointerBlock::FunctionSymbolic(variable) | PointerBlock::Symbolic(variable) => {
            Some(variable)
        }
        PointerBlock::Concrete(_)
        | PointerBlock::StringLiteral { .. }
        | PointerBlock::Function(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::Heap(_) => None,
    };
    if replacement_variable != Some(binder) || !matches!(sort, Sort::CPointer(_)) {
        return (body.clone(), binder);
    }

    let mut reserved = crate::kernel::proposition_variables(body);
    reserved.insert(from);
    reserved.insert(binder);
    reserved.insert(replacement_variable.expect("checked above"));
    let fresh = KernelVariableGenerator::fresh_for(0, reserved).next();
    let pointer = match sort {
        Sort::CPointer(CType::FunctionPointer(_)) => Pointer::symbolic_function(fresh),
        Sort::CPointer(_) => Pointer::symbolic(fresh),
        _ => unreachable!("pointer capture avoidance only handles pointer binders"),
    };
    (
        substitute_pointer_variable_in_proposition(body, binder, &pointer),
        fresh,
    )
}

fn substitute_pointer_variable_in_term(term: &Term, from: Variable, to: &Pointer) -> Term {
    match term {
        Term::Condition(condition) => Term::Condition(substitute_pointer_variable_in_condition(
            condition, from, to,
        )),
        Term::Integer(_) => {
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .term(term)
        }
        Term::Bitvector32(_) | Term::PointerOffset(_) => term.clone(),
        Term::CValue(value) => {
            Term::CValue(substitute_pointer_variable_in_c_value(value, from, to))
        }
        Term::Sequence(sequence) => {
            Term::Sequence(substitute_pointer_variable_in_sequence(sequence, from, to))
        }
        Term::Algebraic(term) => Term::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: substitute_pointer_variable_in_algebraic_term_node(term, from, to),
        }),
        Term::CExpressionOutcome(outcome) => Term::CExpressionOutcome(
            substitute_pointer_variable_in_c_expression_outcome(outcome, from, to),
        ),
        Term::CStatementOutcome(outcome) => Term::CStatementOutcome(
            substitute_pointer_variable_in_c_statement_outcome(outcome, from, to),
        ),
        Term::CFunctionOutcome(outcome) => Term::CFunctionOutcome(
            substitute_pointer_variable_in_c_function_outcome(outcome, from, to),
        ),
        Term::CMemory(memory) => {
            Term::CMemory(substitute_pointer_variable_in_memory(memory, from, to))
        }
        Term::CState(state) => {
            Term::CState(substitute_pointer_variable_in_c_state(state, from, to))
        }
    }
}

fn substitute_pointer_variable_in_algebraic_term_node(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Pointer,
) -> AlgebraicTermNode {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
        AlgebraicTermNode::Constructor { variant, fields } => AlgebraicTermNode::Constructor {
            variant: variant.clone(),
            fields: fields
                .iter()
                .map(|field| substitute_pointer_variable_in_algebraic_value(field, from, to))
                .collect(),
        },
        AlgebraicTermNode::Match { scrutinee, arms } => AlgebraicTermNode::Match {
            scrutinee: Box::new(substitute_pointer_variable_in_algebraic_term(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| AlgebraicResultMatchArm {
                    variant: arm.variant.clone(),
                    bindings: arm
                        .bindings
                        .iter()
                        .map(|binding| {
                            substitute_pointer_variable_in_algebraic_value(binding, from, to)
                        })
                        .collect(),
                    body: substitute_pointer_variable_in_algebraic_term(&arm.body, from, to),
                })
                .collect(),
        },
        AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
            AlgebraicTermNode::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_pointer_variable_in_pure_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
    }
}

fn substitute_pointer_variable_in_algebraic_term(
    term: &AlgebraicTerm,
    from: Variable,
    to: &Pointer,
) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: term.algebraic_type.clone(),
        node: substitute_pointer_variable_in_algebraic_term_node(term, from, to),
    }
}

fn substitute_pointer_variable_in_algebraic_value(
    value: &AlgebraicValue,
    from: Variable,
    to: &Pointer,
) -> AlgebraicValue {
    match value {
        AlgebraicValue::C(value) => {
            AlgebraicValue::C(substitute_pointer_variable_in_c_value(value, from, to))
        }
        AlgebraicValue::Integer(value) => AlgebraicValue::Integer(value.clone()),
        AlgebraicValue::Algebraic(value) => AlgebraicValue::Algebraic(
            substitute_pointer_variable_in_algebraic_term(value, from, to),
        ),
    }
}

fn substitute_pointer_variable_in_pure_function_argument(
    argument: &PureFunctionArgument,
    from: Variable,
    to: &Pointer,
) -> PureFunctionArgument {
    match argument {
        PureFunctionArgument::Integer(value) => PureFunctionArgument::Integer(value.clone()),
        PureFunctionArgument::Value(value) => {
            PureFunctionArgument::Value(substitute_pointer_variable_in_c_value(value, from, to))
        }
        PureFunctionArgument::Algebraic(value) => PureFunctionArgument::Algebraic(
            substitute_pointer_variable_in_algebraic_term(value, from, to),
        ),
        PureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => PureFunctionArgument::ArrayRef {
            memory: substitute_pointer_variable_in_memory(memory, from, to),
            pointer: substitute_pointer_variable_in_c_value(pointer, from, to),
            element_type: *element_type,
        },
    }
}

fn substitute_pointer_variable_in_sequence(
    sequence: &SequenceTerm,
    from: Variable,
    to: &Pointer,
) -> SequenceTerm {
    let node = match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => SequenceTermNode::Literal(
            values
                .iter()
                .map(|value| substitute_pointer_variable_in_c_value(value, from, to))
                .collect::<Vec<_>>()
                .into(),
        ),
        SequenceTermNode::Concat(left, right) => SequenceTermNode::Concat(
            substitute_pointer_variable_in_sequence(left, from, to),
            substitute_pointer_variable_in_sequence(right, from, to),
        ),
    };
    SequenceTerm {
        element_type: sequence.element_type,
        node: std::sync::Arc::new(node),
    }
}

fn substitute_pointer_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Pointer,
) -> ConditionTerm {
    match condition {
        ConditionTerm::IntegerLessThan(..)
        | ConditionTerm::IntegerLessEqual(..)
        | ConditionTerm::IntegerGreaterThan(..)
        | ConditionTerm::IntegerGreaterEqual(..)
        | ConditionTerm::IntegerEqual(..)
        | ConditionTerm::IntegerNotEqual(..) => {
            crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                .condition(condition)
        }
        ConditionTerm::AlgebraicEqual(left, right) => ConditionTerm::AlgebraicEqual(
            Box::new(substitute_pointer_variable_in_algebraic_term(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_algebraic_term(
                right, from, to,
            )),
        ),
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            substitute_pointer_variable_in_pointer(left, from, to),
            substitute_pointer_variable_in_pointer(right, from, to),
        ),
        condition => condition.clone(),
    }
}

fn substitute_pointer_variable_in_c_value(value: &CValue, from: Variable, to: &Pointer) -> CValue {
    let Term::CValue(value) =
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
            .term(&Term::CValue(value.clone()))
    else {
        unreachable!("C value rewriting preserves its carrier")
    };
    value
}

fn substitute_pointer_variable_in_pointer(
    pointer: &Pointer,
    from: Variable,
    to: &Pointer,
) -> Pointer {
    let replaces_block = matches!(
        (&pointer.block, &to.block),
        (PointerBlock::Symbolic(variable), _) | (PointerBlock::FunctionSymbolic(variable), _)
            if *variable == from
    );
    let offset = pointer.offset.clone();
    if replaces_block {
        Pointer {
            block: to.block.clone(),
            offset: PointerOffsetTerm::add(to.offset.clone(), offset),
        }
    } else {
        pointer.clone()
    }
}

fn substitute_pointer_variable_in_c_expression(
    expression: &CExpression,
    from: Variable,
    to: &Pointer,
) -> CExpression {
    match expression {
        CExpression::Value(value) => {
            CExpression::Value(substitute_pointer_variable_in_c_value(value, from, to))
        }
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => expression.clone(),
        CExpression::Cast {
            expression,
            target_type,
            pointee_volatile,
            pointee_constant,
        } => CExpression::Cast {
            expression: Box::new(substitute_pointer_variable_in_c_expression(
                expression, from, to,
            )),
            target_type: *target_type,
            pointee_volatile: *pointee_volatile,
            pointee_constant: *pointee_constant,
        },
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => CExpression::Conditional {
            condition: Box::new(substitute_pointer_variable_in_c_expression(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_pointer_variable_in_c_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_c_expression(
                else_branch,
                from,
                to,
            )),
        },
        CExpression::FloatClassification {
            expression,
            classification,
        } => CExpression::FloatClassification {
            expression: Box::new(substitute_pointer_variable_in_c_expression(
                expression, from, to,
            )),
            classification: *classification,
        },
        CExpression::FloatNegate(expression) => CExpression::FloatNegate(Box::new(
            substitute_pointer_variable_in_c_expression(expression, from, to),
        )),
        CExpression::AddressOf(body) => CExpression::AddressOf(Box::new(
            substitute_pointer_variable_in_c_expression(body, from, to),
        )),
        CExpression::PointerOffsetBytes { pointer, bytes } => CExpression::PointerOffsetBytes {
            pointer: Box::new(substitute_pointer_variable_in_c_expression(
                pointer, from, to,
            )),
            bytes: *bytes,
        },
        CExpression::Load(body) => CExpression::Load(Box::new(
            substitute_pointer_variable_in_c_expression(body, from, to),
        )),
        CExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
        } => CExpression::TypedLoad {
            pointer: Box::new(substitute_pointer_variable_in_c_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
            volatile: *volatile,
        },
        CExpression::Not(body) | CExpression::BitwiseNot(body) => {
            let body = Box::new(substitute_pointer_variable_in_c_expression(body, from, to));
            match expression {
                CExpression::Not(_) => CExpression::Not(body),
                CExpression::BitwiseNot(_) => CExpression::BitwiseNot(body),
                _ => unreachable!("the combined unary expression arm is exhaustive"),
            }
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right)
        | CExpression::Index(left, right) => {
            let left = Box::new(substitute_pointer_variable_in_c_expression(left, from, to));
            let right = Box::new(substitute_pointer_variable_in_c_expression(right, from, to));
            match expression {
                CExpression::LessThan(_, _) => CExpression::LessThan(left, right),
                CExpression::LessEqual(_, _) => CExpression::LessEqual(left, right),
                CExpression::GreaterThan(_, _) => CExpression::GreaterThan(left, right),
                CExpression::GreaterEqual(_, _) => CExpression::GreaterEqual(left, right),
                CExpression::Equal(_, _) => CExpression::Equal(left, right),
                CExpression::NotEqual(_, _) => CExpression::NotEqual(left, right),
                CExpression::And(_, _) => CExpression::And(left, right),
                CExpression::Or(_, _) => CExpression::Or(left, right),
                CExpression::Add(_, _) => CExpression::Add(left, right),
                CExpression::Subtract(_, _) => CExpression::Subtract(left, right),
                CExpression::Multiply(_, _) => CExpression::Multiply(left, right),
                CExpression::Divide(_, _) => CExpression::Divide(left, right),
                CExpression::Remainder(_, _) => CExpression::Remainder(left, right),
                CExpression::ShiftLeft(_, _) => CExpression::ShiftLeft(left, right),
                CExpression::ShiftRight(_, _) => CExpression::ShiftRight(left, right),
                CExpression::BitwiseAnd(_, _) => CExpression::BitwiseAnd(left, right),
                CExpression::BitwiseOr(_, _) => CExpression::BitwiseOr(left, right),
                CExpression::BitwiseXor(_, _) => CExpression::BitwiseXor(left, right),
                CExpression::Index(_, _) => CExpression::Index(left, right),
                _ => unreachable!("the combined binary expression arm is exhaustive"),
            }
        }
    }
}

fn substitute_pointer_variable_in_c_statement(
    statement: &CStatement,
    from: Variable,
    to: &Pointer,
) -> CStatement {
    match statement {
        CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Declare { .. }
        | CStatement::DeclareAggregate { .. } => statement.clone(),
        CStatement::ContinueWithStep { step } => CStatement::ContinueWithStep {
            step: Box::new(substitute_pointer_variable_in_c_statement(step, from, to)),
        },
        CStatement::Assign { name, expression } => CStatement::Assign {
            name: name.clone(),
            expression: substitute_pointer_variable_in_c_expression(expression, from, to),
        },
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => CStatement::CallAssign {
            target: target.clone(),
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_expression(argument, from, to))
                .collect(),
        },
        CStatement::Call {
            function_name,
            arguments,
        } => CStatement::Call {
            function_name: function_name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_expression(argument, from, to))
                .collect(),
        },
        CStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
        } => CStatement::HeapAllocate {
            target: target.clone(),
            bytes: substitute_pointer_variable_in_c_expression(bytes, from, to),
            zeroed: *zeroed,
        },
        CStatement::HeapFree { pointer } => CStatement::HeapFree {
            pointer: substitute_pointer_variable_in_c_expression(pointer, from, to),
        },
        CStatement::Assert { condition, label } => CStatement::Assert {
            condition: substitute_pointer_variable_in_c_expression(condition, from, to),
            label: label.clone(),
        },
        CStatement::Seq(first, second) => c_seq(
            substitute_pointer_variable_in_c_statement(first, from, to),
            substitute_pointer_variable_in_c_statement(second, from, to),
        ),
        CStatement::Return(expression) => CStatement::Return(
            substitute_pointer_variable_in_c_expression(expression, from, to),
        ),
        CStatement::Store { pointer, value } => CStatement::Store {
            pointer: substitute_pointer_variable_in_c_expression(pointer, from, to),
            value: substitute_pointer_variable_in_c_expression(value, from, to),
        },
        CStatement::TypedStore {
            pointer,
            value,
            value_type,
            volatile,
        } => CStatement::TypedStore {
            pointer: substitute_pointer_variable_in_c_expression(pointer, from, to),
            value: substitute_pointer_variable_in_c_expression(value, from, to),
            value_type: *value_type,
            volatile: *volatile,
        },
        CStatement::CopyAggregate {
            target,
            source,
            layout,
        } => CStatement::CopyAggregate {
            target: substitute_pointer_variable_in_c_expression(target, from, to),
            source: substitute_pointer_variable_in_c_expression(source, from, to),
            layout: layout.clone(),
        },
        CStatement::Update {
            target,
            operator,
            operand,
        } => CStatement::Update {
            target: substitute_pointer_variable_in_c_expression(target, from, to),
            operator: *operator,
            operand: substitute_pointer_variable_in_c_expression(operand, from, to),
        },
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => CStatement::If {
            condition: substitute_pointer_variable_in_c_expression(condition, from, to),
            then_branch: Box::new(substitute_pointer_variable_in_c_statement(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_c_statement(
                else_branch,
                from,
                to,
            )),
        },
        CStatement::While {
            condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            do_while,
        } => CStatement::While {
            structural_measure: structural_measure.clone(),
            condition: substitute_pointer_variable_in_c_expression(condition, from, to),
            ranking_measures: ranking_measures
                .iter()
                .map(|measure| substitute_pointer_variable_in_c_expression(measure, from, to))
                .collect(),
            resource_specs: resource_specs
                .iter()
                .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
                .collect(),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_pointer_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            invariant_checks: invariant_checks
                .iter()
                .map(|check| CLoopInvariantCheck {
                    proposition: substitute_pointer_variable_in_spec_proposition(
                        check.proposition(),
                        from,
                        to,
                    ),
                    entry_context: check.entry_context.clone(),
                    preservation_context: check.preservation_context.clone(),
                })
                .collect(),
            effect_checks: effect_checks
                .iter()
                .map(|check| CLoopEffectCheck {
                    effect: substitute_pointer_variable_in_loop_effect(check.effect(), from, to),
                    span: check.span,
                    context: check.context.clone(),
                    origin: check.origin,
                    validated_ranges: check.validated_ranges.as_ref().map(|ranges| {
                        ranges
                            .iter()
                            .map(|range| {
                                substitute_pointer_variable_in_c_memory_range(range, from, to)
                            })
                            .collect()
                    }),
                })
                .collect(),
            do_while: *do_while,
            body: Box::new(substitute_pointer_variable_in_c_statement(body, from, to)),
        },
        CStatement::Switch { expression, cases } => CStatement::Switch {
            expression: substitute_pointer_variable_in_c_expression(expression, from, to),
            cases: cases
                .iter()
                .map(|case| CSwitchCase {
                    value: case.value,
                    body: Box::new(substitute_pointer_variable_in_c_statement(
                        &case.body, from, to,
                    )),
                })
                .collect(),
        },
    }
}

fn substitute_pointer_variable_in_loop_effect(
    effect: &CLoopEffect,
    from: Variable,
    to: &Pointer,
) -> CLoopEffect {
    match effect {
        CLoopEffect::Immutable => CLoopEffect::Immutable,
        CLoopEffect::Mutable(segments) => CLoopEffect::Mutable(
            segments
                .iter()
                .map(|segment| CMemorySegment {
                    base: substitute_pointer_variable_in_c_expression(&segment.base, from, to),
                    start: substitute_pointer_variable_in_c_expression(&segment.start, from, to),
                    end: substitute_pointer_variable_in_c_expression(&segment.end, from, to),
                    element_width: segment.element_width,
                    guard: segment.guard.as_ref().map(|guard| {
                        substitute_pointer_variable_in_spec_proposition(guard, from, to)
                    }),
                })
                .collect(),
        ),
    }
}

fn substitute_pointer_variable_in_c_expression_outcome(
    outcome: &CExpressionOutcome,
    from: Variable,
    to: &Pointer,
) -> CExpressionOutcome {
    match outcome {
        CExpressionOutcome::Value(value) => {
            CExpressionOutcome::Value(substitute_pointer_variable_in_c_value(value, from, to))
        }
        CExpressionOutcome::UndefinedBehavior(kind) => {
            CExpressionOutcome::UndefinedBehavior(kind.clone())
        }
        CExpressionOutcome::RuntimeError(kind) => CExpressionOutcome::RuntimeError(kind.clone()),
    }
}

fn substitute_pointer_variable_in_c_statement_outcome(
    outcome: &CStatementOutcome,
    from: Variable,
    to: &Pointer,
) -> CStatementOutcome {
    match outcome {
        CStatementOutcome::Normal(state) => {
            CStatementOutcome::Normal(substitute_pointer_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Break(state) => {
            CStatementOutcome::Break(substitute_pointer_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Continue(state) => {
            CStatementOutcome::Continue(substitute_pointer_variable_in_c_state(state, from, to))
        }
        CStatementOutcome::Return { value, state } => CStatementOutcome::Return {
            value: substitute_pointer_variable_in_c_value(value, from, to),
            state: substitute_pointer_variable_in_c_state(state, from, to),
        },
        CStatementOutcome::VerificationDiverges => CStatementOutcome::VerificationDiverges,
        CStatementOutcome::UndefinedBehavior(kind) => {
            CStatementOutcome::UndefinedBehavior(kind.clone())
        }
        CStatementOutcome::RuntimeError(kind) => CStatementOutcome::RuntimeError(kind.clone()),
    }
}

fn substitute_pointer_variable_in_c_function_outcome(
    outcome: &CFunctionOutcome,
    from: Variable,
    to: &Pointer,
) -> CFunctionOutcome {
    match outcome {
        CFunctionOutcome::Return { value, state } => CFunctionOutcome::Return {
            value: substitute_pointer_variable_in_c_value(value, from, to),
            state: substitute_pointer_variable_in_c_state(state, from, to),
        },
        CFunctionOutcome::VerificationDiverges => CFunctionOutcome::VerificationDiverges,
        CFunctionOutcome::UndefinedBehavior(kind) => {
            CFunctionOutcome::UndefinedBehavior(kind.clone())
        }
        CFunctionOutcome::RuntimeError(kind) => CFunctionOutcome::RuntimeError(kind.clone()),
    }
}

fn substitute_pointer_variable_in_c_state(state: &CState, from: Variable, to: &Pointer) -> CState {
    let bindings = std::sync::Arc::new(
        state
            .locals
            .bindings
            .iter()
            .map(|(name, binding)| {
                let binding = match binding {
                    CLocalBinding::Object {
                        value,
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::Object {
                        value: substitute_pointer_variable_in_c_value(value, from, to),
                        c_type: *c_type,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::UninitializedObject {
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::UninitializedObject {
                        c_type: *c_type,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::GlobalObject {
                        c_type,
                        slot,
                        volatile,
                        pointee_volatile,
                        constant,
                        pointee_constant,
                    } => CLocalBinding::GlobalObject {
                        c_type: *c_type,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        volatile: *volatile,
                        pointee_volatile: *pointee_volatile,
                        constant: *constant,
                        pointee_constant: *pointee_constant,
                    },
                    CLocalBinding::ArrayObject {
                        element_type,
                        length,
                        slot,
                        constant,
                    } => CLocalBinding::ArrayObject {
                        element_type: *element_type,
                        length: *length,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        constant: *constant,
                    },
                    CLocalBinding::AggregateObject {
                        layout,
                        slot,
                        constant,
                    } => CLocalBinding::AggregateObject {
                        layout: layout.clone(),
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        constant: *constant,
                    },
                };
                (name.clone(), binding)
            })
            .collect(),
    );
    let slots = std::sync::Arc::new(
        state
            .locals
            .slots
            .iter()
            .map(|(pointer, name)| {
                (
                    substitute_pointer_variable_in_pointer(pointer, from, to),
                    name.clone(),
                )
            })
            .collect(),
    );
    CState {
        locals: CLocalEnvironment { bindings, slots },
        memory: substitute_pointer_variable_in_memory(&state.memory, from, to),
        resource_bindings: state.resource_bindings.clone(),
        instance_field_scope: substitute_pointer_variable_in_resource_context(
            &state.instance_field_scope,
            from,
            to,
        ),
        resources: substitute_pointer_variable_in_resource_context(&state.resources, from, to),
        next_local_frame: state.next_local_frame,
        next_local_lifetime: state.next_local_lifetime,
        counted_populations: std::sync::Arc::new(
            state
                .counted_populations
                .iter()
                .map(|population| CCountedPopulation {
                    name: population.name.clone(),
                    arguments: population
                        .arguments
                        .iter()
                        .map(|argument| {
                            substitute_pointer_variable_in_algebraic_value(argument, from, to)
                        })
                        .collect(),
                    count: population.count.clone(),
                    family_observation_marker: population.family_observation_marker,
                })
                .collect(),
        ),
    }
}

fn substitute_pointer_variable_in_resource_context(
    resources: &ResourceContext,
    from: Variable,
    to: &Pointer,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_facts(
        resources
            .facts()
            .iter()
            .map(|resource| substitute_pointer_variable_in_resource(resource, from, to)),
    )
}

fn substitute_pointer_variable_in_resource(
    resource: &CResourceFact,
    from: Variable,
    to: &Pointer,
) -> CResourceFact {
    match resource {
        CResourceFact::Own(resource, quantity) => CResourceFact::Own(
            substitute_pointer_variable_in_c_resource(resource, from, to),
            quantity.clone(),
        ),
        CResourceFact::View(resource) => CResourceFact::View(
            substitute_pointer_variable_in_c_resource(resource, from, to),
        ),
    }
}

fn substitute_pointer_variable_in_c_resource(
    resource: &CResource,
    from: Variable,
    to: &Pointer,
) -> CResource {
    match resource {
        CResource::Instance(instance) => {
            let mut result = instance.clone();
            result.arguments = instance
                .arguments
                .iter()
                .map(|value| substitute_pointer_variable_in_algebraic_value(value, from, to))
                .collect();
            result.fields = instance
                .fields
                .iter()
                .map(|value| substitute_pointer_variable_in_algebraic_value(value, from, to))
                .collect();
            CResource::Instance(result)
        }
        CResource::Memory(range) => CResource::Memory(
            substitute_pointer_variable_in_c_memory_range(range, from, to),
        ),
        CResource::Composite { name, arguments } => CResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_algebraic_value(argument, from, to))
                .collect(),
        },
        CResource::Token { name, arguments } => CResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_algebraic_value(argument, from, to))
                .collect(),
        },
    }
}

fn substitute_pointer_variable_in_c_memory_range(
    range: &CMemoryRange,
    from: Variable,
    to: &Pointer,
) -> CMemoryRange {
    range.with_bounds(
        substitute_pointer_variable_in_pointer(&range.base, from, to),
        range.start.clone(),
        range.end.clone(),
    )
}

fn substitute_pointer_variable_in_c_memory_segment(
    segment: &CMemorySegment,
    from: Variable,
    to: &Pointer,
) -> CMemorySegment {
    CMemorySegment {
        base: substitute_pointer_variable_in_c_expression(&segment.base, from, to),
        start: substitute_pointer_variable_in_c_expression(&segment.start, from, to),
        end: substitute_pointer_variable_in_c_expression(&segment.end, from, to),
        element_width: segment.element_width,
        guard: segment
            .guard
            .as_ref()
            .map(|guard| substitute_pointer_variable_in_spec_proposition(guard, from, to)),
    }
}

fn substitute_pointer_variable_in_memory(
    memory: &CMemory,
    from: Variable,
    to: &Pointer,
) -> CMemory {
    CMemory {
        blocks: std::sync::Arc::new(
            memory
                .blocks
                .iter()
                .map(|(block, contents)| {
                    (
                        substitute_pointer_variable_in_block(block, from, to),
                        contents.clone(),
                    )
                })
                .collect(),
        ),
        cells: std::sync::Arc::new(
            memory
                .cells
                .iter()
                .map(|(pointer, value)| {
                    (
                        substitute_pointer_variable_in_pointer(pointer, from, to),
                        substitute_pointer_variable_in_c_value(value, from, to),
                    )
                })
                .collect(),
        ),
        union_cells: std::sync::Arc::new(
            memory
                .union_cells
                .iter()
                .map(|((pointer, c_type), value)| {
                    (
                        (
                            substitute_pointer_variable_in_pointer(pointer, from, to),
                            *c_type,
                        ),
                        substitute_pointer_variable_in_c_value(value, from, to),
                    )
                })
                .collect(),
        ),
        ended_local_blocks: std::sync::Arc::new(
            memory
                .ended_local_blocks
                .iter()
                .map(|block| substitute_pointer_variable_in_block(block, from, to))
                .collect(),
        ),
        heap: std::sync::Arc::new(CHeapMemory {
            live_allocations: memory
                .heap
                .live_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        bytes.clone(),
                    )
                })
                .collect(),
            deallocated_allocations: memory
                .heap
                .deallocated_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        bytes.clone(),
                    )
                })
                .collect(),
            pending_allocations: memory
                .heap
                .pending_allocations
                .iter()
                .map(|(base, bytes)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        bytes.clone(),
                    )
                })
                .collect(),
            uninitialized_allocations: memory
                .heap
                .uninitialized_allocations
                .iter()
                .map(|base| substitute_pointer_variable_in_pointer(base, from, to))
                .collect(),
            zeroed_allocations: memory
                .heap
                .zeroed_allocations
                .iter()
                .map(|base| substitute_pointer_variable_in_pointer(base, from, to))
                .collect(),
            zeroed_prefix_allocations: memory
                .heap
                .zeroed_prefix_allocations
                .iter()
                .map(|(base, prefix)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        prefix.clone(),
                    )
                })
                .collect(),
            zeroed_pending_allocations: memory
                .heap
                .zeroed_pending_allocations
                .iter()
                .map(|base| substitute_pointer_variable_in_pointer(base, from, to))
                .collect(),
            pending_reallocations: memory
                .heap
                .pending_reallocations
                .iter()
                .map(|(base, pending)| {
                    (
                        substitute_pointer_variable_in_pointer(base, from, to),
                        CPendingReallocation {
                            old_pointer: substitute_pointer_variable_in_pointer(
                                &pending.old_pointer,
                                from,
                                to,
                            ),
                            old_bytes: pending.old_bytes.clone(),
                            zeroed_prefix: pending.zeroed_prefix.clone(),
                            copied_cells: pending
                                .copied_cells
                                .iter()
                                .map(|(offset, value)| {
                                    (
                                        offset.clone(),
                                        substitute_pointer_variable_in_c_value(value, from, to),
                                    )
                                })
                                .collect(),
                        },
                    )
                })
                .collect(),
        }),
    }
}

fn substitute_pointer_variable_in_block(
    block: &PointerBlock,
    from: Variable,
    to: &Pointer,
) -> PointerBlock {
    match block {
        PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable)
            if *variable == from =>
        {
            to.block.clone()
        }
        block => block.clone(),
    }
}

fn substitute_pointer_variable_in_spec_memory(
    memory: &SpecMemory,
    from: Variable,
    to: &Pointer,
) -> SpecMemory {
    match memory {
        SpecMemory::Current => SpecMemory::Current,
        SpecMemory::FunctionEntry => SpecMemory::FunctionEntry,
        SpecMemory::LoopEntry => SpecMemory::LoopEntry,
        SpecMemory::Fixed(memory) => {
            SpecMemory::Fixed(substitute_pointer_variable_in_memory(memory, from, to))
        }
    }
}

fn substitute_pointer_variable_in_spec_algebraic_expression(
    expression: &SpecAlgebraicExpression,
    from: Variable,
    to: &Pointer,
) -> SpecAlgebraicExpression {
    let node = match &expression.node {
        SpecAlgebraicExpressionNode::ResourceField(projection) => {
            SpecAlgebraicExpressionNode::ResourceField(projection.clone())
        }
        SpecAlgebraicExpressionNode::Variable(variable) => {
            SpecAlgebraicExpressionNode::Variable(*variable)
        }
        SpecAlgebraicExpressionNode::Binding(name) => {
            SpecAlgebraicExpressionNode::Binding(name.clone())
        }
        SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
            SpecAlgebraicExpressionNode::Constructor {
                variant: variant.clone(),
                fields: fields
                    .iter()
                    .map(|field| match field {
                        SpecAlgebraicValue::C(field) => SpecAlgebraicValue::C(
                            substitute_pointer_variable_in_spec_expression(field, from, to),
                        ),
                        SpecAlgebraicValue::Integer(field) => {
                            SpecAlgebraicValue::Integer(field.clone())
                        }
                        SpecAlgebraicValue::Algebraic(field) => SpecAlgebraicValue::Algebraic(
                            substitute_pointer_variable_in_spec_algebraic_expression(
                                field, from, to,
                            ),
                        ),
                    })
                    .collect(),
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            SpecAlgebraicExpressionNode::Match {
                scrutinee: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                    scrutinee, from, to,
                )),
                arms: arms
                    .iter()
                    .map(|arm| SpecAlgebraicResultMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        body: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                            &arm.body, from, to,
                        )),
                    })
                    .collect(),
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
            SpecAlgebraicExpressionNode::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_pointer_variable_in_spec_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
    };
    SpecAlgebraicExpression {
        algebraic_type: expression.algebraic_type.clone(),
        node,
    }
}

fn substitute_pointer_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Pointer,
) -> SpecExpression {
    match expression {
        SpecExpression::ResourceField { .. } => expression.clone(),
        SpecExpression::IntegerToMachine { value, destination } => {
            SpecExpression::IntegerToMachine {
                value: Box::new(substitute_pointer_variable_in_spec_integer(value, from, to)),
                destination: *destination,
            }
        }
        SpecExpression::Value(value) => {
            SpecExpression::Value(substitute_pointer_variable_in_c_value(value, from, to))
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => SpecExpression::AlgebraicMatch {
            scrutinee: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                scrutinee, from, to,
            )),
            arms: arms
                .iter()
                .map(|arm| SpecAlgebraicMatchArm {
                    variant: arm.variant.clone(),
                    bindings: arm.bindings.clone(),
                    binding_types: arm.binding_types.clone(),
                    body: substitute_pointer_variable_in_spec_expression(&arm.body, from, to),
                })
                .collect(),
        },
        SpecExpression::CExpression(expression) => SpecExpression::CExpression(
            substitute_pointer_variable_in_c_expression(expression, from, to),
        ),
        SpecExpression::CountedResourceCount { name, arguments } => {
            SpecExpression::CountedResourceCount {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        argument.as_ref().map(|argument| {
                            substitute_pointer_variable_in_spec_expression(argument, from, to)
                        })
                    })
                    .collect(),
            }
        }
        SpecExpression::Add(left, right)
        | SpecExpression::Subtract(left, right)
        | SpecExpression::Multiply(left, right)
        | SpecExpression::Divide(left, right)
        | SpecExpression::Remainder(left, right)
        | SpecExpression::ShiftLeft(left, right)
        | SpecExpression::ShiftRight(left, right)
        | SpecExpression::BitwiseAnd(left, right)
        | SpecExpression::BitwiseOr(left, right)
        | SpecExpression::BitwiseXor(left, right) => {
            let left = Box::new(substitute_pointer_variable_in_spec_expression(
                left, from, to,
            ));
            let right = Box::new(substitute_pointer_variable_in_spec_expression(
                right, from, to,
            ));
            match expression {
                SpecExpression::Add(_, _) => SpecExpression::Add(left, right),
                SpecExpression::Subtract(_, _) => SpecExpression::Subtract(left, right),
                SpecExpression::Multiply(_, _) => SpecExpression::Multiply(left, right),
                SpecExpression::Divide(_, _) => SpecExpression::Divide(left, right),
                SpecExpression::Remainder(_, _) => SpecExpression::Remainder(left, right),
                SpecExpression::ShiftLeft(_, _) => SpecExpression::ShiftLeft(left, right),
                SpecExpression::ShiftRight(_, _) => SpecExpression::ShiftRight(left, right),
                SpecExpression::BitwiseAnd(_, _) => SpecExpression::BitwiseAnd(left, right),
                SpecExpression::BitwiseOr(_, _) => SpecExpression::BitwiseOr(left, right),
                SpecExpression::BitwiseXor(_, _) => SpecExpression::BitwiseXor(left, right),
                _ => unreachable!("the combined spec binary arm is exhaustive"),
            }
        }
        SpecExpression::BitwiseNot(expression) => SpecExpression::BitwiseNot(Box::new(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        )),
        SpecExpression::Cast(expression, target_type) => SpecExpression::Cast(
            Box::new(substitute_pointer_variable_in_spec_expression(
                expression, from, to,
            )),
            *target_type,
        ),
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => SpecExpression::If {
            condition: Box::new(substitute_pointer_variable_in_spec_proposition(
                condition, from, to,
            )),
            then_branch: Box::new(substitute_pointer_variable_in_spec_expression(
                then_branch,
                from,
                to,
            )),
            else_branch: Box::new(substitute_pointer_variable_in_spec_expression(
                else_branch,
                from,
                to,
            )),
        },
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => SpecExpression::RangeFold {
            start: Box::new(substitute_pointer_variable_in_spec_expression(
                start, from, to,
            )),
            end: Box::new(substitute_pointer_variable_in_spec_expression(
                end, from, to,
            )),
            initial: Box::new(substitute_pointer_variable_in_spec_expression(
                initial, from, to,
            )),
            accumulator: accumulator.clone(),
            item: item.clone(),
            body: Box::new(substitute_pointer_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::Let { name, value, body } => SpecExpression::Let {
            name: name.clone(),
            value: Box::new(substitute_pointer_variable_in_spec_expression(
                value, from, to,
            )),
            body: Box::new(substitute_pointer_variable_in_spec_expression(
                body, from, to,
            )),
        },
        SpecExpression::PureFunctionApplication {
            name,
            arguments,
            result_type,
        } => SpecExpression::PureFunctionApplication {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| {
                    substitute_pointer_variable_in_spec_function_argument(argument, from, to)
                })
                .collect(),
            result_type: *result_type,
        },
        SpecExpression::LoopEntrySnapshot(expression) => {
            SpecExpression::LoopEntrySnapshot(Box::new(
                substitute_pointer_variable_in_spec_expression(expression, from, to),
            ))
        }
        SpecExpression::PointerOffset {
            pointer,
            elements,
            byte_width,
        } => SpecExpression::PointerOffset {
            pointer: Box::new(substitute_pointer_variable_in_spec_expression(
                pointer, from, to,
            )),
            elements: Box::new(substitute_pointer_variable_in_spec_expression(
                elements, from, to,
            )),
            byte_width: *byte_width,
        },
        SpecExpression::MemoryLoad {
            memory,
            pointer,
            value_type,
        } => SpecExpression::MemoryLoad {
            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
            pointer: Box::new(substitute_pointer_variable_in_spec_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
        },
    }
}

fn substitute_pointer_variable_in_spec_function_argument(
    argument: &SpecPureFunctionArgument,
    from: Variable,
    to: &Pointer,
) -> SpecPureFunctionArgument {
    match argument {
        SpecPureFunctionArgument::Integer(value) => SpecPureFunctionArgument::Integer(
            substitute_pointer_variable_in_spec_integer(value, from, to),
        ),
        SpecPureFunctionArgument::Value(expression) => SpecPureFunctionArgument::Value(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        ),
        SpecPureFunctionArgument::Algebraic(expression) => SpecPureFunctionArgument::Algebraic(
            substitute_pointer_variable_in_spec_algebraic_expression(expression, from, to),
        ),
        SpecPureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => SpecPureFunctionArgument::ArrayRef {
            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
            pointer: substitute_pointer_variable_in_spec_expression(pointer, from, to),
            element_type: *element_type,
        },
    }
}

fn substitute_pointer_variable_in_spec_integer(
    expression: &SpecIntegerExpression,
    from: Variable,
    to: &Pointer,
) -> SpecIntegerExpression {
    match expression {
        SpecIntegerExpression::ResourceField(_) => expression.clone(),
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            SpecIntegerExpression::AlgebraicMatch {
                scrutinee: Box::new(substitute_pointer_variable_in_spec_algebraic_expression(
                    scrutinee, from, to,
                )),
                arms: arms
                    .iter()
                    .map(|arm| SpecIntegerMatchArm {
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        binding_variables: arm.binding_variables.clone(),
                        body: Box::new(substitute_pointer_variable_in_spec_integer(
                            &arm.body, from, to,
                        )),
                    })
                    .collect(),
            }
        }
        SpecIntegerExpression::PureFunctionApplication { name, arguments } => {
            SpecIntegerExpression::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_pointer_variable_in_spec_function_argument(argument, from, to)
                    })
                    .collect(),
            }
        }
        SpecIntegerExpression::Term(term) => {
            let Term::Integer(term) =
                crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_variable(from, to)
                    .term(&Term::Integer(term.clone()))
            else {
                unreachable!()
            };
            SpecIntegerExpression::Term(term)
        }
        SpecIntegerExpression::FromMachine(value) => SpecIntegerExpression::FromMachine(Box::new(
            substitute_pointer_variable_in_spec_expression(value, from, to),
        )),
        SpecIntegerExpression::Negate(value) => SpecIntegerExpression::Negate(Box::new(
            substitute_pointer_variable_in_spec_integer(value, from, to),
        )),
        SpecIntegerExpression::Add(left, right) => SpecIntegerExpression::Add(
            Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
        ),
        SpecIntegerExpression::Subtract(left, right) => SpecIntegerExpression::Subtract(
            Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
        ),
        SpecIntegerExpression::Multiply(left, right) => SpecIntegerExpression::Multiply(
            Box::new(substitute_pointer_variable_in_spec_integer(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_integer(right, from, to)),
        ),
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let index = match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                    SpecIntegerRangeFoldIndex::Int32 {
                        start: Box::new(substitute_pointer_variable_in_spec_expression(
                            start, from, to,
                        )),
                        end: Box::new(substitute_pointer_variable_in_spec_expression(
                            end, from, to,
                        )),
                    }
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    SpecIntegerRangeFoldIndex::Integer {
                        start: Box::new(substitute_pointer_variable_in_spec_integer(
                            start, from, to,
                        )),
                        end: Box::new(substitute_pointer_variable_in_spec_integer(end, from, to)),
                    }
                }
            };
            SpecIntegerExpression::RangeFold {
                index,
                initial: Box::new(substitute_pointer_variable_in_spec_integer(
                    initial, from, to,
                )),
                accumulator: *accumulator,
                item: *item,
                body: Box::new(substitute_pointer_variable_in_spec_integer(body, from, to)),
            }
        }
    }
}

fn substitute_pointer_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &Pointer,
) -> SpecProposition {
    match proposition {
        SpecProposition::ForAllInteger {
            name,
            variable,
            body,
        } => SpecProposition::ForAllInteger {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::IntegerComparison {
            left,
            operator,
            right,
        } => SpecProposition::IntegerComparison {
            left: substitute_pointer_variable_in_spec_integer(left, from, to),
            operator: *operator,
            right: substitute_pointer_variable_in_spec_integer(right, from, to),
        },
        SpecProposition::AlgebraicComparison { left, equal, right } => {
            SpecProposition::AlgebraicComparison {
                left: substitute_pointer_variable_in_spec_algebraic_expression(left, from, to),
                equal: *equal,
                right: substitute_pointer_variable_in_spec_algebraic_expression(right, from, to),
            }
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            SpecProposition::SequenceMembership {
                element: substitute_pointer_variable_in_spec_expression(element, from, to),
                sequence: substitute_pointer_variable_in_spec_sequence(sequence, from, to),
            }
        }
        SpecProposition::SequenceComparison { left, equal, right } => {
            SpecProposition::SequenceComparison {
                left: substitute_pointer_variable_in_spec_sequence(left, from, to),
                equal: *equal,
                right: substitute_pointer_variable_in_spec_sequence(right, from, to),
            }
        }
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => SpecProposition::Comparison {
            left: substitute_pointer_variable_in_spec_expression(left, from, to),
            operator: *operator,
            right: substitute_pointer_variable_in_spec_expression(right, from, to),
        },
        SpecProposition::FloatClassification {
            expression,
            classification,
        } => SpecProposition::FloatClassification {
            expression: substitute_pointer_variable_in_spec_expression(expression, from, to),
            classification: *classification,
        },
        SpecProposition::And(left, right) => SpecProposition::And(
            Box::new(substitute_pointer_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Or(left, right) => SpecProposition::Or(
            Box::new(substitute_pointer_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::Not(body) => SpecProposition::Not(Box::new(
            substitute_pointer_variable_in_spec_proposition(body, from, to),
        )),
        SpecProposition::Implies(left, right) => SpecProposition::Implies(
            Box::new(substitute_pointer_variable_in_spec_proposition(
                left, from, to,
            )),
            Box::new(substitute_pointer_variable_in_spec_proposition(
                right, from, to,
            )),
        ),
        SpecProposition::ForAllInt32 {
            name,
            variable,
            body,
        } => SpecProposition::ForAllInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ForAllPointer {
            name,
            variable,
            c_type,
            body,
        } => SpecProposition::ForAllPointer {
            name: name.clone(),
            variable: *variable,
            c_type: *c_type,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsInteger {
            name,
            variable,
            body,
        } => SpecProposition::ExistsInteger {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsInt32 {
            name,
            variable,
            body,
        } => SpecProposition::ExistsInt32 {
            name: name.clone(),
            variable: *variable,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::ExistsPointer {
            name,
            variable,
            c_type,
            body,
        } => SpecProposition::ExistsPointer {
            name: name.clone(),
            variable: *variable,
            c_type: *c_type,
            body: Box::new(substitute_pointer_variable_in_spec_proposition(
                body, from, to,
            )),
        },
        SpecProposition::Predicate { name, arguments } => SpecProposition::Predicate {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| match argument {
                    SpecPredicateArgument::Value(expression) => SpecPredicateArgument::Value(
                        substitute_pointer_variable_in_spec_expression(expression, from, to),
                    ),
                    SpecPredicateArgument::ArrayRef { memory, pointer } => {
                        SpecPredicateArgument::ArrayRef {
                            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
                            pointer: substitute_pointer_variable_in_spec_expression(
                                pointer, from, to,
                            ),
                        }
                    }
                })
                .collect(),
        },
        SpecProposition::ResourceSeparate { left, right } => SpecProposition::ResourceSeparate {
            left: substitute_pointer_variable_in_spec_resource(left, from, to),
            right: substitute_pointer_variable_in_spec_resource(right, from, to),
        },
        SpecProposition::ResourceContains { parent, child } => SpecProposition::ResourceContains {
            parent: substitute_pointer_variable_in_spec_resource(parent, from, to),
            child: substitute_pointer_variable_in_spec_resource(child, from, to),
        },
        SpecProposition::MemoryLoadable {
            memory,
            base,
            start,
            end,
            element_width,
        } => SpecProposition::MemoryLoadable {
            memory: substitute_pointer_variable_in_spec_memory(memory, from, to),
            base: substitute_pointer_variable_in_spec_expression(base, from, to),
            start: substitute_pointer_variable_in_spec_expression(start, from, to),
            end: substitute_pointer_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        SpecProposition::Defined(expression) => SpecProposition::Defined(
            substitute_pointer_variable_in_spec_expression(expression, from, to),
        ),
    }
}

fn substitute_pointer_variable_in_spec_sequence(
    sequence: &SpecSequenceExpression,
    from: Variable,
    to: &Pointer,
) -> SpecSequenceExpression {
    match sequence {
        SpecSequenceExpression::Literal(elements) => SpecSequenceExpression::Literal(
            elements
                .iter()
                .map(|element| substitute_pointer_variable_in_spec_expression(element, from, to))
                .collect(),
        ),
        SpecSequenceExpression::Concat(left, right) => SpecSequenceExpression::Concat(
            Box::new(substitute_pointer_variable_in_spec_sequence(left, from, to)),
            Box::new(substitute_pointer_variable_in_spec_sequence(
                right, from, to,
            )),
        ),
    }
}

fn substitute_pointer_variable_in_spec_resource(
    resource: &SpecResource,
    from: Variable,
    to: &Pointer,
) -> SpecResource {
    match resource {
        SpecResource::Memory {
            base,
            start,
            end,
            element_width,
        } => SpecResource::Memory {
            base: substitute_pointer_variable_in_spec_expression(base, from, to),
            start: substitute_pointer_variable_in_spec_expression(start, from, to),
            end: substitute_pointer_variable_in_spec_expression(end, from, to),
            element_width: *element_width,
        },
        SpecResource::Composite { name, arguments } => SpecResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_spec_expression(argument, from, to))
                .collect(),
        },
        SpecResource::Token { name, arguments } => SpecResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_spec_expression(argument, from, to))
                .collect(),
        },
    }
}

fn substitute_pointer_variable_in_c_function(
    function: &CFunction,
    from: Variable,
    to: &Pointer,
) -> CFunction {
    let mut interface = function.contract_interface().clone();
    interface.resource_requires = function
        .resource_requires()
        .iter()
        .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
        .collect();
    interface.resource_ensures = function
        .resource_ensures()
        .iter()
        .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
        .collect();
    interface.resource_constructors = function
        .resource_constructors()
        .iter()
        .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
        .collect();
    interface.contract_requires = function
        .contract_requires()
        .iter()
        .map(|proposition| substitute_pointer_variable_in_spec_proposition(proposition, from, to))
        .collect();
    interface.contract_ensures = function
        .contract_ensures()
        .iter()
        .map(|proposition| substitute_pointer_variable_in_spec_proposition(proposition, from, to))
        .collect();
    interface.contract_mutable = function
        .contract_mutable()
        .iter()
        .map(|segment| substitute_pointer_variable_in_c_memory_segment(segment, from, to))
        .collect();
    interface.resource_derived_mutable_segments = function
        .contract_interface()
        .resource_derived_mutable_segments
        .iter()
        .map(|segment| substitute_pointer_variable_in_c_memory_segment(segment, from, to))
        .collect();
    interface.composite_resource_definitions = function
        .composite_resource_definitions()
        .iter()
        .map(|definition| CCompositeResourceDefinition {
            instance_schema: definition.instance_schema.clone(),
            name: definition.name.clone(),
            parameters: definition.parameters.clone(),
            witnesses: definition.witnesses.clone(),
            condition: definition.condition.as_ref().map(|condition| {
                substitute_pointer_variable_in_spec_proposition(condition, from, to)
            }),
            matched: definition.matched.as_ref().map(|body| CResourceMatchBody {
                field_index: body.field_index,
                algebraic_type: body.algebraic_type.clone(),
                arms: body
                    .arms
                    .iter()
                    .map(|arm| CResourceMatchArm {
                        children: arm
                            .children
                            .iter()
                            .map(|child| CResourceChildSpec {
                                name: child.name.clone(),
                                resource: child.resource.clone(),
                                binding: child.binding,
                                field_bindings: child.field_bindings.clone(),
                                arguments: child
                                    .arguments
                                    .iter()
                                    .map(|argument| {
                                        substitute_pointer_variable_in_c_expression(
                                            argument, from, to,
                                        )
                                    })
                                    .collect(),
                            })
                            .collect(),
                        variant: arm.variant.clone(),
                        bindings: arm.bindings.clone(),
                        binding_types: arm.binding_types.clone(),
                        binding_variables: arm.binding_variables.clone(),
                        contains: arm
                            .contains
                            .iter()
                            .map(|resource| {
                                substitute_pointer_variable_in_resource_spec(resource, from, to)
                            })
                            .collect(),
                        facts: arm
                            .facts
                            .iter()
                            .map(|fact| {
                                substitute_pointer_variable_in_spec_proposition(fact, from, to)
                            })
                            .collect(),
                    })
                    .collect(),
            }),
            recursive: definition.recursive,
            matched_recursive: definition.matched_recursive,
            counted_population: definition.counted_population,
            contains: definition
                .contains
                .iter()
                .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
                .collect(),
            facts: definition
                .facts
                .iter()
                .map(|fact| substitute_pointer_variable_in_spec_proposition(fact, from, to))
                .collect(),
        })
        .collect();
    interface.predicate_unfoldings = function
        .predicate_unfoldings()
        .iter()
        .map(|unfolding| CPredicateUnfolding {
            predicate: substitute_pointer_variable_in_spec_proposition(
                &unfolding.predicate,
                from,
                to,
            ),
            body: substitute_pointer_variable_in_spec_proposition(&unfolding.body, from, to),
        })
        .collect();
    CFunction {
        program_entry: function.program_entry,
        name: function.name.clone(),
        inline_body: function.inline_body,
        body: substitute_pointer_variable_in_c_statement(function.body(), from, to),
        source_body: substitute_pointer_variable_in_c_statement(function.source_body(), from, to),
        contract_interface: interface,
        global_variables: function.global_variables.clone(),
        global_arrays: function.global_arrays.clone(),
        static_variables: function.static_variables.clone(),
        static_storage: function.static_storage.clone(),
        string_literals: function.string_literals.clone(),
    }
}

fn substitute_pointer_variable_in_resource_spec(
    resource: &CResourceSpec,
    from: Variable,
    to: &Pointer,
) -> CResourceSpec {
    CResourceSpec::new(
        substitute_pointer_variable_in_resource_term(resource.term(), from, to),
        resource.access(),
        match resource.quantity() {
            CResourceQuantity::One => CResourceQuantity::One,
            CResourceQuantity::Count(quantity) => CResourceQuantity::Count(
                substitute_pointer_variable_in_c_expression(quantity, from, to),
            ),
        },
        resource.role(),
        resource.snapshot(),
    )
    .expect("pointer substitution preserves resource validity")
}

fn substitute_pointer_variable_in_resource_term(
    resource: &CResourceTerm,
    from: Variable,
    to: &Pointer,
) -> CResourceTerm {
    match resource {
        CResourceTerm::Instance {
            identity,
            binder,
            schema,
            resource,
        } => CResourceTerm::Instance {
            identity: *identity,
            binder: binder.clone(),
            schema: schema.clone(),
            resource: Box::new(substitute_pointer_variable_in_resource_term(
                resource, from, to,
            )),
        },
        CResourceTerm::Memory(segment) => CResourceTerm::Memory(CMemorySegment {
            base: substitute_pointer_variable_in_c_expression(&segment.base, from, to),
            start: substitute_pointer_variable_in_c_expression(&segment.start, from, to),
            end: substitute_pointer_variable_in_c_expression(&segment.end, from, to),
            element_width: segment.element_width,
            guard: segment
                .guard
                .as_ref()
                .map(|guard| substitute_pointer_variable_in_spec_proposition(guard, from, to)),
        }),
        CResourceTerm::Composite {
            name,
            arguments,
            parameter_types,
        } => CResourceTerm::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
        CResourceTerm::Token {
            name,
            arguments,
            parameter_types,
        } => CResourceTerm::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
    }
}

fn substitute_pointer_variable_in_c_function_specification(
    specification: &CFunctionSpecification,
    from: Variable,
    to: &Pointer,
) -> CFunctionSpecification {
    CFunctionSpecification {
        state: substitute_pointer_variable_in_c_state(specification.state(), from, to),
        arguments: specification
            .arguments()
            .iter()
            .map(|argument| substitute_pointer_variable_in_c_expression(argument, from, to))
            .collect(),
        requires: specification
            .requires()
            .iter()
            .map(|requirement| substitute_pointer_variable_in_proposition(requirement, from, to))
            .collect(),
        outcome: substitute_pointer_variable_in_c_function_outcome(
            specification.outcome(),
            from,
            to,
        ),
    }
}

#[cfg(test)]
mod pointee_const_return_tests {
    use super::*;

    #[test]
    fn pointee_const_return_value_substitution_preserves_qualifiers_and_identity() {
        let value = CValue::typed_pointer(Pointer::symbolic(Variable(918)), CType::Int32Pointer)
            .with_pointer_pointee_constant(true)
            .with_pointer_pointee_volatile(true);
        assert_eq!(
            substitute_bitvector_variable_in_c_value(
                &value,
                Variable(919),
                &Bitvector32Term::Constant(0)
            ),
            value
        );
        assert_eq!(
            substitute_pointer_variable_in_c_value(&value, Variable(919), &Pointer::null()),
            value
        );
        let replaced =
            substitute_pointer_variable_in_c_value(&value, Variable(918), &Pointer::null());
        assert!(matches!(replaced, CValue::Pointer(pointer)
            if pointer.is_null() && pointer.pointee_constant() && pointer.pointee_volatile()));
    }

    #[test]
    fn pointee_const_return_survives_both_substitutions() {
        let function = CFunction::new(
            CType::UInt8Pointer,
            "text",
            Vec::new(),
            c_return(c_int32_literal(0)),
        )
        .with_return_pointee_constant(true);
        assert!(
            substitute_bitvector_variable_in_c_function(
                &function,
                Variable(914),
                &Bitvector32Term::Constant(0),
            )
            .return_pointee_is_constant()
        );
        assert!(
            substitute_pointer_variable_in_c_function(
                &function,
                Variable(914),
                &Pointer::symbolic(Variable(915)),
            )
            .return_pointee_is_constant()
        );
    }
}

#[cfg(test)]
mod integer_to_machine_substitution_tests {
    use super::*;

    #[test]
    fn integer_to_machine_substitution_descends_math_payload_and_keeps_destination() {
        let payload = crate::kernel::SharedIntegerTerm::from(IntegerTerm::Machine(
            crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(701)),
            ),
        ));
        let term = Bitvector32Term::IntegerToMachine {
            value: payload.clone(),
            destination: crate::kernel::MachineIntegerType::UInt32,
        };
        let replaced = substitute_bitvector_variable(
            &term,
            Variable(701),
            &Bitvector32Term::Variable(Variable(702)),
        );
        let Bitvector32Term::IntegerToMachine { value, destination } = replaced else {
            panic!("substitution changed the carrier shape")
        };
        assert_eq!(destination, crate::kernel::MachineIntegerType::UInt32);
        assert!(matches!(value.as_ref(), IntegerTerm::Machine(machine)
            if machine.ty() == crate::kernel::MachineIntegerType::Int32
                && machine.value() == &Bitvector32Term::Variable(Variable(702))));
    }

    #[test]
    fn integer_to_machine_substitution_reuses_unchanged_shared_payload() {
        let payload = crate::kernel::SharedIntegerTerm::from(IntegerTerm::Variable(Variable(703)));
        let term = Bitvector32Term::IntegerToMachine {
            value: payload.clone(),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let replaced =
            substitute_bitvector_variable(&term, Variable(704), &Bitvector32Term::Constant(0));
        let Bitvector32Term::IntegerToMachine { value, .. } = replaced else {
            panic!("substitution changed the carrier shape")
        };
        assert_eq!(value.id(), payload.id());
    }
}

#[cfg(test)]
mod machine_integer_pointer_substitution_tests {
    use super::*;

    #[test]
    fn pointer_substitution_reaches_integer_observations_and_composes_offsets() {
        let binder = Variable(610);
        let source = Pointer {
            block: PointerBlock::Symbolic(binder),
            offset: PointerOffsetTerm::Constant(8),
        };
        let replacement = Pointer {
            block: PointerBlock::Symbolic(Variable(611)),
            offset: PointerOffsetTerm::Constant(4),
        };
        let expected = Pointer {
            block: replacement.block.clone(),
            offset: PointerOffsetTerm::Constant(12),
        };
        let bits = Bitvector32Term::PointerAddress(Box::new(source));
        let term =
            IntegerTerm::from_machine(crate::kernel::MachineIntegerType::UInt64, bits.clone())
                .unwrap();
        let proposition = Proposition::ConditionIs(
            ConditionTerm::integer_equal(term, IntegerTerm::constant_i64(0)),
            true,
        );
        let rewritten =
            substitute_pointer_variable_in_proposition(&proposition, binder, &replacement);
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, _), true) = rewritten else {
            panic!("unexpected proposition")
        };
        let IntegerTerm::Machine(observation) = left.as_ref() else {
            panic!("missing observation")
        };
        assert_eq!(
            observation.value(),
            &Bitvector32Term::PointerAddress(Box::new(expected.clone()))
        );

        let spec = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::FromMachine(Box::new(SpecExpression::Value(
                CValue::UInt64(bits),
            ))),
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
        };
        let rewritten =
            substitute_pointer_variable_in_spec_proposition(&spec, binder, &replacement);
        let SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::FromMachine(value),
            ..
        } = rewritten
        else {
            panic!("unexpected spec proposition")
        };
        assert_eq!(
            *value,
            SpecExpression::Value(CValue::UInt64(Bitvector32Term::PointerAddress(Box::new(
                expected
            ))))
        );
    }
}

#[cfg(test)]
mod integer_function_traversal_tests {
    use super::*;

    #[test]
    fn integer_applications_rewrite_c_and_nested_integer_arguments() {
        let from = Variable(817);
        let machine = Bitvector32Term::Variable(from);
        let make = |machine: Bitvector32Term| {
            IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                "observed".into(),
                vec![
                    PureFunctionArgument::Value(CValue::Int32(machine.clone())),
                    PureFunctionArgument::Integer(
                        IntegerTerm::from_machine(MachineIntegerType::Int32, machine)
                            .unwrap()
                            .into(),
                    ),
                ],
            ))
        };
        let original = make(machine);
        let expected = make(Bitvector32Term::Variable(Variable(818)));
        assert_eq!(
            substitute_bitvector_variable_in_integer(
                &original,
                from,
                &Bitvector32Term::Variable(Variable(818))
            ),
            expected
        );
        assert_eq!(
            crate::kernel::proof::term_rewrite::TermRewrite::for_bits(
                &Bitvector32Term::Variable(from),
                &Bitvector32Term::Variable(Variable(818))
            )
            .term(&Term::Integer(original)),
            Term::Integer(expected)
        );
    }

    #[test]
    fn shared_integer_application_substitution_scales_with_dag_size() {
        let from = Variable(831);
        let mut samples = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut term: SharedIntegerTerm = IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(from),
            )
            .unwrap()
            .into();
            for _ in 0..depth {
                term = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    "pair".into(),
                    vec![
                        PureFunctionArgument::Integer(term.clone()),
                        PureFunctionArgument::Integer(term),
                    ],
                ))
                .into();
            }
            let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &term,
                    from,
                    &Bitvector32Term::Variable(Variable(832)),
                )
            });
            assert_ne!(&changed, term.as_ref());
            assert!(work > 0);
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "application substitution expanded the DAG: {samples:?}"
            );
        }
    }

    #[test]
    fn public_integer_substitution_keeps_array_ref_snapshots_opaque() {
        let source = Variable(840);
        let pointer = CValue::Pointer(CPointerValue::new(
            Pointer {
                block: PointerBlock::Symbolic(Variable(841)),
                offset: PointerOffsetTerm::Constant(0),
            },
            CType::VoidPointer,
        ));
        let make_memory = |count: u64| {
            let mut memory = CMemory::new().with_block("array", 8);
            for index in 0..count {
                memory = memory.with_block(PointerBlock::Heap(index + 1), 8);
            }
            memory
        };
        let make = |memory: CMemory| {
            Proposition::Equal(
                Term::Integer(IntegerTerm::PureFunctionApplication(
                    SharedIntegerApplication::intern(
                        "observe_array".into(),
                        vec![
                            PureFunctionArgument::Integer(IntegerTerm::var(source).into()),
                            PureFunctionArgument::ArrayRef {
                                memory,
                                pointer: pointer.clone(),
                                element_type: CType::UInt8,
                            },
                        ],
                    ),
                )),
                Term::Integer(IntegerTerm::constant_i64(0)),
            )
        };
        let small_memory = make_memory(0);
        let large_memory = make_memory(256);
        let (small, small_work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_integer_variable_in_pure_proposition(
                &make(small_memory.clone()),
                source,
                &IntegerTerm::constant_i64(7),
            )
            .expect("small snapshot substitution should be supported")
        });
        let (large, large_work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_integer_variable_in_pure_proposition(
                &make(large_memory.clone()),
                source,
                &IntegerTerm::constant_i64(7),
            )
            .expect("large snapshot substitution should be supported")
        });
        let snapshot = |proposition: Proposition| {
            let Proposition::Equal(Term::Integer(value), _) = proposition else {
                panic!("expected Integer equality")
            };
            let IntegerTerm::PureFunctionApplication(application) = value else {
                panic!("expected pure Integer application")
            };
            let [
                PureFunctionArgument::Integer(integer),
                PureFunctionArgument::ArrayRef { memory, .. },
            ] = application.arguments()
            else {
                panic!("expected Integer and ArrayRef arguments")
            };
            assert!(matches!(integer.as_ref(), IntegerTerm::Constant(_)));
            memory.clone()
        };
        assert!(std::sync::Arc::ptr_eq(
            &snapshot(small).blocks,
            &small_memory.blocks
        ));
        assert!(std::sync::Arc::ptr_eq(
            &snapshot(large).blocks,
            &large_memory.blocks
        ));
        assert_eq!(small_work, large_work);
    }
}

#[cfg(test)]
mod integer_match_substitution_scope_tests {
    use super::*;

    fn symbolic_match(body: IntegerTerm, binding: Variable) -> IntegerTerm {
        symbolic_match_with_binding(
            body,
            AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(binding))),
        )
    }

    fn symbolic_match_with_binding(body: IntegerTerm, binding: AlgebraicValue) -> IntegerTerm {
        let scrutinee = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("MatchInput".into()),
            node: AlgebraicTermNode::Variable(Variable(9000)),
        };
        IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Arm".into(),
                bindings: vec![binding],
                body: body.into(),
            }],
        }
    }

    fn shared_symbolic_match(body: IntegerTerm, binding: Variable) -> IntegerTerm {
        let scrutinee = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("SharedMatchInput".into()),
            node: AlgebraicTermNode::Variable(Variable(9060)),
        };
        IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                AlgebraicIntegerMatchArm {
                    variant: "Left".into(),
                    bindings: vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
                        binding,
                    )))],
                    body: body.clone().into(),
                },
                AlgebraicIntegerMatchArm {
                    variant: "Right".into(),
                    bindings: vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
                        binding,
                    )))],
                    body: body.into(),
                },
            ],
        }
    }

    #[test]
    fn substitution_freshens_match_binder_while_preserving_free_replacement() {
        let x = Variable(9001);
        let y = Variable(9002);
        let body = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(y))),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(x))),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(Variable(
                    9003,
                )))),
            ],
        ));
        let rewritten = substitute_bitvector_variable_in_integer(
            &symbolic_match(body, y),
            x,
            &Bitvector32Term::Variable(y),
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
            panic!("expected algebraic match")
        };
        let AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(fresh))) =
            arms[0].bindings[0]
        else {
            panic!("expected C binder")
        };
        assert_ne!(fresh, y);
        let IntegerTerm::PureFunctionApplication(application) = arms[0].body.as_ref() else {
            panic!("expected application body")
        };
        let [
            PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(first))),
            PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(second))),
            PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(free))),
        ] = application.arguments()
        else {
            panic!("expected two C arguments")
        };
        assert_eq!(*first, fresh);
        assert_eq!(*second, y);
        assert_eq!(*free, Variable(9003));
        assert_ne!(fresh, Variable(9003));
    }

    #[test]
    fn substitution_reserves_match_binders_on_the_rhs_before_rewriting_lhs() {
        let source = Variable(9030);
        let replacement = Variable(9031);
        let free = Variable(9032);
        let rhs = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: AlgebraicType::parameter("RhsMatchInput".into()),
                node: AlgebraicTermNode::Variable(free),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Arm".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::var(replacement))],
                body: IntegerTerm::Add(
                    IntegerTerm::var(replacement).into(),
                    IntegerTerm::var(free).into(),
                )
                .into(),
            }],
        };
        let proposition =
            Proposition::Equal(Term::Integer(IntegerTerm::var(source)), Term::Integer(rhs));
        let rewritten = substitute_integer_variable_in_pure_proposition(
            &proposition,
            source,
            &IntegerTerm::var(replacement),
        )
        .expect("Integer substitution should preserve the RHS match");
        let Proposition::Equal(Term::Integer(left), Term::Integer(right)) = rewritten else {
            panic!("expected Integer equality")
        };
        assert_eq!(left, IntegerTerm::var(replacement));
        let IntegerTerm::AlgebraicMatch { arms, .. } = right else {
            panic!("expected RHS algebraic match")
        };
        let AlgebraicValue::Integer(IntegerTerm::Variable(fresh)) = arms[0].bindings[0] else {
            panic!("expected Integer match binder")
        };
        assert_ne!(fresh, replacement);
        assert_ne!(fresh, free);
        assert_eq!(
            arms[0].body.as_ref(),
            &IntegerTerm::Add(
                IntegerTerm::var(fresh).into(),
                IntegerTerm::var(free).into()
            )
        );
    }

    #[test]
    fn substitution_does_not_rewrite_a_match_binder_or_its_bound_body() {
        let y = Variable(9010);
        let z = Variable(9011);
        let body = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
            "observe".into(),
            vec![PureFunctionArgument::Value(CValue::Int32(
                Bitvector32Term::Variable(y),
            ))],
        ));
        let rewritten = substitute_bitvector_variable_in_integer(
            &symbolic_match(body, y),
            y,
            &Bitvector32Term::Variable(z),
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
            panic!("expected algebraic match")
        };
        assert_eq!(
            arms[0].bindings[0],
            AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(y),))
        );
        let IntegerTerm::PureFunctionApplication(application) = arms[0].body.as_ref() else {
            panic!("expected application body")
        };
        assert_eq!(
            application.arguments(),
            &[PureFunctionArgument::Value(CValue::Int32(
                Bitvector32Term::Variable(y),
            ))]
        );
    }

    #[test]
    fn substitution_freshens_each_integral_match_carrier() {
        let source = Variable(9040);
        let replacement = Variable(9041);
        let carriers = [
            CValue::Bool(Bitvector32Term::Variable(replacement)),
            CValue::Int16(Bitvector32Term::Variable(replacement)),
            CValue::Int32(Bitvector32Term::Variable(replacement)),
            CValue::UInt8(Bitvector32Term::Variable(replacement)),
            CValue::UInt16(Bitvector32Term::Variable(replacement)),
            CValue::UInt32(Bitvector32Term::Variable(replacement)),
            CValue::Int64(Bitvector32Term::Variable(replacement)),
            CValue::UInt64(Bitvector32Term::Variable(replacement)),
        ];
        for carrier in carriers {
            let body = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                "observe".into(),
                vec![PureFunctionArgument::Value(CValue::Int32(
                    Bitvector32Term::Variable(source),
                ))],
            ));
            let rewritten = substitute_bitvector_variable_in_integer(
                &symbolic_match_with_binding(body, AlgebraicValue::C(carrier.clone())),
                source,
                &Bitvector32Term::Variable(replacement),
            );
            let IntegerTerm::AlgebraicMatch { arms, .. } = rewritten else {
                panic!("expected algebraic match")
            };
            assert_ne!(arms[0].bindings[0], AlgebraicValue::C(carrier));
        }
    }

    #[test]
    fn match_substitution_shared_function_dag_scales_linearly() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let mut body = IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(9050)),
            )
            .unwrap();
            for _ in 0..depth {
                body = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    "pair".into(),
                    vec![
                        PureFunctionArgument::Integer(body.clone().into()),
                        PureFunctionArgument::Integer(body.into()),
                    ],
                ));
            }
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &symbolic_match(body, Variable(9051)),
                    Variable(9050),
                    &Bitvector32Term::Variable(Variable(9052)),
                )
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "function DAG expanded: {work:?}");
        }
    }

    #[test]
    fn nested_match_construction_and_diagnostics_preserve_sharing() {
        for depth in [8usize, 16, 32, 64] {
            let mut body = IntegerTerm::constant_i64(1);
            for _ in 0..depth {
                body = shared_symbolic_match(body, Variable(9070));
                let IntegerTerm::AlgebraicMatch { arms, .. } = &body else {
                    unreachable!()
                };
                assert_eq!(arms[0].body.id(), arms[1].body.id());
            }
            let copy = body.clone();
            assert_eq!(copy, body);
            let diagnostic = format!("{copy:?}");
            assert!(
                diagnostic.len() < depth * 500,
                "diagnostic expanded a shared match graph"
            );
        }
    }

    #[test]
    fn match_substitution_shared_bodies_scale_linearly() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let mut body = IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(9020)),
            )
            .unwrap();
            for _ in 0..depth {
                body = shared_symbolic_match(body, Variable(9021));
            }
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_bitvector_variable_in_integer(
                    &symbolic_match(body, Variable(9021)),
                    Variable(9020),
                    &Bitvector32Term::Variable(Variable(9022)),
                )
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "match substitution expanded: {work:?}"
            );
        }
    }
}

#[cfg(test)]
mod integer_mixed_quantifier_tests {
    use super::*;

    fn application(integer: IntegerTerm, machine: Bitvector32Term) -> IntegerTerm {
        IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
            "opaque".into(),
            vec![
                PureFunctionArgument::Integer(integer.into()),
                PureFunctionArgument::Value(CValue::Int32(machine)),
            ],
        ))
    }

    #[test]
    fn integer_substitution_descends_function_and_reverse_conversion_arguments() {
        let from = Variable(87);
        let converted = Bitvector32Term::IntegerToMachine {
            value: IntegerTerm::var(from).into(),
            destination: MachineIntegerType::Int32,
        };
        let source = Proposition::Equal(
            Term::Integer(application(IntegerTerm::var(from), converted)),
            Term::Integer(IntegerTerm::var(from)),
        );
        let result = substitute_integer_variable_in_pure_proposition(
            &source,
            from,
            &IntegerTerm::constant_i64(9),
        )
        .unwrap();
        assert_eq!(
            result,
            Proposition::Equal(
                Term::Integer(application(
                    IntegerTerm::constant_i64(9),
                    Bitvector32Term::IntegerToMachine {
                        value: IntegerTerm::constant_i64(9).into(),
                        destination: MachineIntegerType::Int32,
                    }
                )),
                Term::Integer(IntegerTerm::constant_i64(9)),
            )
        );
    }

    #[test]
    fn integer_atom_capture_avoidance_preserves_c_variable_carrier() {
        let from = Variable(88);
        let bound = Variable(89);
        let source = Proposition::ForAll {
            var: bound,
            sort: Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(application(
                    IntegerTerm::var(from),
                    Bitvector32Term::Variable(bound),
                )),
                Term::Integer(IntegerTerm::var(bound)),
            )),
        };
        let result = substitute_integer_variable_in_pure_proposition(
            &source,
            from,
            &IntegerTerm::var(bound),
        )
        .unwrap();
        let Proposition::ForAll {
            var: fresh, body, ..
        } = result
        else {
            panic!("quantifier lost")
        };
        assert_ne!(fresh, bound);
        assert_eq!(
            *body,
            Proposition::Equal(
                Term::Integer(application(
                    IntegerTerm::var(bound),
                    Bitvector32Term::Variable(bound)
                )),
                Term::Integer(IntegerTerm::var(fresh)),
            )
        );
    }

    #[test]
    fn integer_function_quantifier_substitution_preserves_shared_dags() {
        let from = Variable(90);
        let mut work = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut value = IntegerTerm::var(from);
            for _ in 0..depth {
                let child: SharedIntegerTerm = value.into();
                value = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    "pair".into(),
                    vec![
                        PureFunctionArgument::Integer(child.clone()),
                        PureFunctionArgument::Integer(child),
                    ],
                ));
            }
            let source = Proposition::Equal(
                Term::Integer(value),
                Term::Integer(IntegerTerm::constant_i64(0)),
            );
            let (result, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_integer_variable_in_pure_proposition(
                    &source,
                    from,
                    &IntegerTerm::constant_i64(2),
                )
                .unwrap()
            });
            let Proposition::Equal(Term::Integer(mut value), _) = result else {
                panic!("equality lost")
            };
            for _ in 0..depth {
                let IntegerTerm::PureFunctionApplication(application) = value else {
                    panic!("application lost")
                };
                let [
                    PureFunctionArgument::Integer(left),
                    PureFunctionArgument::Integer(right),
                ] = application.arguments()
                else {
                    panic!("arguments lost")
                };
                assert_eq!(left.id(), right.id());
                value = left.as_ref().clone();
            }
            assert_eq!(value, IntegerTerm::constant_i64(2));
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(pair[1] <= pair[0] * 3, "{work:?}");
        }
    }

    #[test]
    fn integer_witness_replacement_reserves_registered_pointer_integer() {
        let memory = crate::kernel::intern_c_memory(
            crate::kernel::CMemory::new().with_block("integer-witness-capture", 64),
        );
        let source = Variable(9_100);
        // This ID is intentionally shared by the replacement's registered
        // pointer and the nested Integer binder. The pointer occurrence is
        // free in the replacement even though the load itself is opaque.
        let free_index = Variable(9_101);
        let load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &Pointer {
                block: PointerBlock::Concrete("integer-witness-capture".into()),
                offset: PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::IntegerToMachine {
                        value: IntegerTerm::var(free_index).into(),
                        destination: MachineIntegerType::Int32,
                    }),
                    byte_width: 4,
                },
            },
        );
        let replacement = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load),
        ));
        let proposition = Proposition::Exists {
            name: "nested".into(),
            var: free_index,
            sort: Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(IntegerTerm::var(source)),
                Term::Integer(IntegerTerm::var(free_index)),
            )),
        };

        let rewritten =
            substitute_integer_variable_in_pure_proposition(&proposition, source, &replacement)
                .expect("registered-load replacement should remain a valid Integer term");
        let Proposition::Exists {
            var: fresh, body, ..
        } = rewritten
        else {
            panic!("existential binder was dropped")
        };
        assert_ne!(
            fresh, free_index,
            "replacement pointer variable was not reserved"
        );
        let Proposition::Equal(Term::Integer(left), Term::Integer(right)) = *body else {
            panic!("witness body changed carrier")
        };
        assert_eq!(right, IntegerTerm::var(fresh));
        let IntegerTerm::Machine(machine) = left else {
            panic!("witness replacement changed Integer carrier")
        };
        let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
            panic!("registered load was expanded into the memory snapshot")
        };
        let (rewritten_memory, rewritten_pointer) =
            crate::kernel::eval::registered_load_for_variable(rewritten_load)
                .expect("replacement load must retain its defining pointer");
        assert_eq!(rewritten_memory, memory);
        assert!(matches!(
            rewritten_pointer.offset,
            PointerOffsetTerm::Int32Scaled { value, .. }
                if matches!(value.as_ref(), Bitvector32Term::IntegerToMachine { value, .. }
                    if matches!(value.as_ref(), IntegerTerm::Variable(variable)
                if *variable == free_index))
        ));
    }

    fn c_int_equality(left: Variable, right: Variable) -> Proposition {
        Proposition::Equal(
            Term::Bitvector32(Bitvector32Term::Variable(left)),
            Term::Bitvector32(Bitvector32Term::Variable(right)),
        )
    }

    #[test]
    fn integer_substitution_freshens_nested_c_binder_by_carrier() {
        let source = Variable(9_200);
        let c_binder = Variable(9_201);
        let replacement = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(c_binder),
        ));
        let proposition = Proposition::ForAll {
            var: c_binder,
            sort: Sort::CInt32,
            body: Box::new(Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(source)),
                    Term::Integer(IntegerTerm::constant_i64(0)),
                )),
                Box::new(c_int_equality(c_binder, c_binder)),
            )),
        };

        let Proposition::ForAll {
            var: fresh, body, ..
        } = substitute_integer_variable_in_pure_proposition(&proposition, source, &replacement)
            .expect("nested C quantifiers should be rewritten")
        else {
            panic!("C quantifier was lost")
        };
        assert_ne!(fresh, c_binder);
        let Proposition::And(integer_goal, c_goal) = *body else {
            panic!("nested C proposition shape changed")
        };
        assert!(matches!(
            *integer_goal,
            Proposition::Equal(
                Term::Integer(IntegerTerm::Machine(_)),
                Term::Integer(IntegerTerm::Constant(_))
            )
        ));
        assert_eq!(*c_goal, c_int_equality(fresh, fresh));
    }

    #[test]
    fn integer_source_is_not_shadowed_by_same_id_c_binder() {
        let source = Variable(9_210);
        let proposition = Proposition::ForAll {
            var: source,
            sort: Sort::CInt32,
            body: Box::new(Proposition::And(
                Box::new(Proposition::Equal(
                    Term::Integer(IntegerTerm::var(source)),
                    Term::Integer(IntegerTerm::constant_i64(0)),
                )),
                Box::new(c_int_equality(source, source)),
            )),
        };
        let Proposition::ForAll { var, body, .. } =
            substitute_integer_variable_in_pure_proposition(
                &proposition,
                source,
                &IntegerTerm::constant_i64(7),
            )
            .expect("same-ID C binder must not block Integer substitution")
        else {
            panic!("C quantifier was lost")
        };
        assert_eq!(var, source);
        let Proposition::And(integer_goal, c_goal) = *body else {
            panic!("nested C proposition shape changed")
        };
        assert_eq!(
            *integer_goal,
            Proposition::Equal(
                Term::Integer(IntegerTerm::constant_i64(7)),
                Term::Integer(IntegerTerm::constant_i64(0)),
            )
        );
        assert_eq!(*c_goal, c_int_equality(source, source));
    }

    #[test]
    fn integer_substitution_preserves_nested_c_integer_pointer_scopes() {
        let source = Variable(9_220);
        let outer_c = Variable(9_221);
        let inner_integer = outer_c;
        let inner_pointer = Variable(9_222);
        let replacement = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            Bitvector32Term::PointerAddress(Box::new(Pointer::symbolic(inner_pointer))),
        )
        .expect("pointer observations are Integer-valued");
        let pointer_value = |variable| {
            Term::CValue(CValue::Pointer(CPointerValue::new(
                Pointer::symbolic(variable),
                CType::Int32Pointer,
            )))
        };
        let proposition = Proposition::ForAll {
            var: outer_c,
            sort: Sort::CInt32,
            body: Box::new(Proposition::Exists {
                name: "inner".into(),
                var: inner_integer,
                sort: Sort::Integer,
                body: Box::new(Proposition::ForAll {
                    var: inner_pointer,
                    sort: Sort::CPointer(CType::Int32Pointer),
                    body: Box::new(Proposition::And(
                        Box::new(Proposition::Equal(
                            Term::Integer(IntegerTerm::var(source)),
                            Term::Integer(IntegerTerm::var(inner_integer)),
                        )),
                        Box::new(Proposition::Equal(
                            pointer_value(outer_c),
                            pointer_value(inner_pointer),
                        )),
                    )),
                }),
            }),
        };
        let Proposition::ForAll {
            var: outer_after,
            body,
            ..
        } = substitute_integer_variable_in_pure_proposition(&proposition, source, &replacement)
            .expect("nested C/Integer/pointer scopes should be rewritten")
        else {
            panic!("outer C quantifier was lost")
        };
        assert_eq!(outer_after, outer_c);
        let Proposition::Exists {
            var: integer_after,
            body,
            ..
        } = *body
        else {
            panic!("Integer quantifier was lost")
        };
        assert_eq!(integer_after, inner_integer);
        let Proposition::ForAll {
            var: pointer_after,
            body,
            ..
        } = *body
        else {
            panic!("pointer quantifier was lost")
        };
        assert_ne!(pointer_after, inner_pointer);
        let Proposition::And(integer_goal, pointer_goal) = *body else {
            panic!("nested scope proposition shape changed")
        };
        assert!(matches!(
            *integer_goal,
            Proposition::Equal(Term::Integer(IntegerTerm::Machine(_)), Term::Integer(_))
        ));
        assert_eq!(
            *pointer_goal,
            Proposition::Equal(pointer_value(outer_c), pointer_value(pointer_after))
        );
    }

    #[test]
    fn integer_substitution_rejects_non_term_nested_sort() {
        let proposition = Proposition::ForAll {
            var: Variable(9_230),
            sort: Sort::Condition,
            body: Box::new(Proposition::Equal(
                Term::Integer(IntegerTerm::var(Variable(9_231))),
                Term::Integer(IntegerTerm::constant_i64(0)),
            )),
        };
        assert_eq!(
            substitute_integer_variable_in_pure_proposition(
                &proposition,
                Variable(9_231),
                &IntegerTerm::constant_i64(1),
            ),
            Err(IntegerPureSubstitutionError::UnsupportedSort)
        );
    }

    #[test]
    fn integer_substitution_nested_carrier_scopes_scale_with_shared_body() {
        let source = Variable(9_240);
        let mut work = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut body = Proposition::Equal(
                Term::Integer(IntegerTerm::var(source)),
                Term::Integer(IntegerTerm::constant_i64(0)),
            );
            for index in (0..depth).rev() {
                let variable = Variable(9_300 + (index / 2) as u64);
                body = if index % 2 == 0 {
                    Proposition::ForAll {
                        var: variable,
                        sort: Sort::CInt32,
                        body: Box::new(body),
                    }
                } else {
                    Proposition::Exists {
                        name: format!("integer{index}"),
                        var: variable,
                        sort: Sort::Integer,
                        body: Box::new(body),
                    }
                };
            }
            let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
                substitute_integer_variable_in_pure_proposition(
                    &body,
                    source,
                    &IntegerTerm::constant_i64(3),
                )
                .expect("nested carrier scopes should remain bounded")
            });
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "nested scope rewrite expanded: {work:?}"
            );
        }
    }
}

#[cfg(test)]
mod integer_range_fold_substitution_tests {
    use super::*;

    fn int32_index(start: Bitvector32Term, end: Bitvector32Term) -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(start),
            end: SharedIntegerRangeEndpoint::intern(end),
        }
    }

    fn c_item(value: Variable) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(value),
        ))
    }

    fn c_item_value(value: Bitvector32Term) -> IntegerTerm {
        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            value,
        ))
    }

    #[test]
    fn int32_fold_substitution_freshens_item_and_preserves_free_replacement_and_y_plus_one() {
        let source = Variable(70_000);
        let item = Variable(70_001);
        let free_y_plus_one = Variable(70_002);
        let free_zero = Variable(0);
        let accumulator = Variable(70_003);
        let body = IntegerTerm::add(
            IntegerTerm::add(
                IntegerTerm::add(c_item(source), c_item(item)),
                c_item(free_y_plus_one),
            ),
            c_item(free_zero),
        );
        let fold = IntegerTerm::range_fold(
            int32_index(Bitvector32Term::Constant(0), Bitvector32Term::Constant(1)),
            IntegerTerm::var(accumulator),
            accumulator,
            item,
            body,
        );

        let replaced = substitute_bitvector_variable_in_integer(
            &fold,
            source,
            &Bitvector32Term::Variable(item),
        );
        let IntegerTerm::RangeFold {
            item: fresh_item,
            body,
            ..
        } = replaced
        else {
            panic!("substitution changed the fold shape")
        };
        assert_ne!(fresh_item, item);
        assert_ne!(fresh_item, free_y_plus_one);
        assert_ne!(fresh_item, free_zero);
        let IntegerTerm::Add(left, free_zero_term) = body.as_ref() else {
            panic!("missing fold body additions")
        };
        assert!(
            matches!(free_zero_term.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(free_zero))
        );
        let IntegerTerm::Add(prefix, free_item) = left.as_ref() else {
            panic!("missing free y+1 term")
        };
        assert!(matches!(free_item.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(free_y_plus_one)));
        let IntegerTerm::Add(replaced_source, bound_item) = prefix.as_ref() else {
            panic!("missing source and item terms")
        };
        assert!(
            matches!(replaced_source.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(item))
        );
        assert!(matches!(bound_item.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(fresh_item)));
    }

    #[test]
    fn int32_fold_substitution_keeps_bound_item_but_rewrites_endpoints_and_initial() {
        let source = Variable(70_010);
        let accumulator = Variable(70_011);
        let body = c_item(source);
        let fold = IntegerTerm::range_fold(
            int32_index(
                Bitvector32Term::Variable(source),
                Bitvector32Term::Variable(source),
            ),
            c_item(source),
            accumulator,
            source,
            body,
        );

        let replaced =
            substitute_bitvector_variable_in_integer(&fold, source, &Bitvector32Term::Constant(9));
        let IntegerTerm::RangeFold {
            index,
            initial,
            item,
            body,
            ..
        } = replaced
        else {
            panic!("substitution changed the fold shape")
        };
        assert_eq!(item, source);
        let IntegerRangeFoldIndex::Int32 { start, end } = index else {
            panic!("substitution changed the index carrier")
        };
        assert_eq!(start.value(), &Bitvector32Term::Constant(9));
        assert_eq!(end.value(), &Bitvector32Term::Constant(9));
        assert!(matches!(initial.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Constant(9)));
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(source)));
    }

    #[test]
    fn unchanged_nested_fold_body_reuses_shared_dag_nodes() {
        let accumulator = Variable(70_020);
        let item = Variable(70_021);
        let nested_body = IntegerTerm::add(IntegerTerm::var(accumulator), IntegerTerm::var(item));
        let nested = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            nested_body,
        );
        let outer = IntegerTerm::add(nested.clone(), nested);
        let replaced = substitute_bitvector_variable_in_integer(
            &outer,
            Variable(70_022),
            &Bitvector32Term::Constant(9),
        );
        let IntegerTerm::Add(left, right) = replaced else {
            panic!("substitution changed the shared outer shape")
        };
        assert_eq!(left.id(), right.id());
    }

    #[test]
    fn integer_substitution_shared_nested_folds_scales_with_dag_size() {
        let from = Variable(70_040);
        let accumulator = Variable(70_041);
        let item = Variable(70_042);
        for depth in [8, 16, 32, 64] {
            let mut value = IntegerTerm::var(from);
            for _ in 0..depth {
                let body = IntegerTerm::add(value.clone(), value.clone());
                value = IntegerTerm::range_fold(
                    IntegerRangeFoldIndex::Integer {
                        start: IntegerTerm::constant_i64(0).into(),
                        end: IntegerTerm::constant_i64(1).into(),
                    },
                    IntegerTerm::constant_i64(0),
                    accumulator,
                    item,
                    body,
                );
            }
            let proposition = Proposition::Equal(
                Term::Integer(value),
                Term::Integer(IntegerTerm::constant_i64(0)),
            );
            let replaced = substitute_integer_variable_in_pure_proposition(
                &proposition,
                from,
                &IntegerTerm::constant_i64(2),
            )
            .expect("fold substitution should preserve the supported Integer carrier");
            let Proposition::Equal(Term::Integer(mut value), _) = replaced else {
                panic!("equality carrier changed")
            };
            for _ in 0..depth {
                let IntegerTerm::RangeFold { body, .. } = value else {
                    panic!("nested fold shape changed")
                };
                let IntegerTerm::Add(left, right) = body.as_ref() else {
                    panic!("shared fold body shape changed")
                };
                assert_eq!(left.id(), right.id());
                value = left.as_ref().clone();
            }
            assert_eq!(value, IntegerTerm::Constant(2.into()));
        }
    }

    #[test]
    fn int32_fold_substitution_rejects_non_machine_item_value() {
        let item = Variable(70_050);
        let body = c_item(item);
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_051),
            &IntegerTerm::constant_i64(0),
            item,
            &IntegerTerm::var(Variable(70_052)),
            true,
        );
        assert_eq!(
            result,
            Err(IntegerPureSubstitutionError::UnsupportedCarrier)
        );
    }

    #[test]
    fn int32_fold_substitution_rejects_wrong_width_machine_item_value() {
        let item = Variable(70_053);
        let body = c_item(item);
        let malformed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            Bitvector32Term::Variable(Variable(70_054)),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_055),
            &IntegerTerm::constant_i64(0),
            item,
            &malformed,
            true,
        );
        assert_eq!(
            result,
            Err(IntegerPureSubstitutionError::UnsupportedCarrier)
        );
    }

    #[test]
    fn int32_fold_substitution_rewrites_registered_load_address_only() {
        let item = Variable(70_056);
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
        let pointer = Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(item)),
                byte_width: 4,
            },
        };
        let load_variable = crate::kernel::eval::load_variable_for_cell(&memory, &pointer);
        let (source_snapshot, _) =
            crate::kernel::eval::registered_load_for_variable(&load_variable)
                .expect("the source load must be registered");
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load_variable),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_057),
            &IntegerTerm::constant_i64(0),
            item,
            &c_item_value(Bitvector32Term::Constant(0)),
            true,
        )
        .expect("the checked fold step should preserve the registered load");
        let IntegerTerm::Machine(machine) = result else {
            panic!("the machine load carrier was lost");
        };
        let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
            panic!("the registered load was not reminted");
        };
        assert_ne!(*rewritten_load, load_variable);
        let (snapshot, pointer) = crate::kernel::eval::registered_load_for_variable(rewritten_load)
            .expect("the rewritten load must remain registered");
        assert_eq!(snapshot, source_snapshot);
        assert_eq!(pointer.offset, PointerOffsetTerm::Constant(0));
    }

    #[test]
    fn int32_fold_substitution_canonicalizes_nonzero_load_base() {
        let item = Variable(70_058);
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("array", 16));
        let pointer = Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Constant(4)),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(item)),
                    byte_width: 4,
                }),
            ),
        };
        let load_variable = crate::kernel::eval::load_variable_for_cell(&memory, &pointer);
        let (source_snapshot, _) =
            crate::kernel::eval::registered_load_for_variable(&load_variable)
                .expect("the source load must be registered");
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(load_variable),
        ));
        let result = instantiate_integer_range_fold_step(
            &body,
            Variable(70_059),
            &IntegerTerm::constant_i64(0),
            item,
            &c_item_value(Bitvector32Term::Constant(0)),
            true,
        )
        .expect("the checked fold step should preserve the registered load");
        let IntegerTerm::Machine(machine) = result else {
            panic!("the machine load carrier was lost");
        };
        let Bitvector32Term::Variable(rewritten_load) = machine.value() else {
            panic!("the registered load was not reminted");
        };
        assert_ne!(*rewritten_load, load_variable);
        let (snapshot, pointer) = crate::kernel::eval::registered_load_for_variable(rewritten_load)
            .expect("the rewritten load must remain registered");
        assert_eq!(snapshot, source_snapshot);
        assert_eq!(pointer.offset, PointerOffsetTerm::Constant(4));
    }

    #[test]
    fn checked_machine_fold_substitution_rejects_work_exhaustion() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};

        let source = Variable(70_060);
        let mut payload = Bitvector32Term::Variable(source);
        for _ in 0..64 {
            payload =
                Bitvector32Term::Add(Box::new(payload), Box::new(Bitvector32Term::Constant(1)));
        }
        let term = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            payload,
        ));
        let (result, _events) = instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 4,
                smart: 4,
                control: 4,
            },
            || {
                instrumentation::collect(|| {
                    let tactic = TacticEvent {
                        claim: "integer fold checked substitution".into(),
                        tactic_index: 0,
                        tactic_name: "integer_fold_checked_substitution".into(),
                        class: "simple".into(),
                        statement_index: 0,
                        source_index: 0,
                    };
                    instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                    let result = substitute_bitvector_variable_in_integer_checked(
                        &term,
                        source,
                        &Bitvector32Term::Constant(7),
                    );
                    instrumentation::emit(VerificationEvent::TacticFailed(tactic));
                    result
                })
            },
        );
        assert_eq!(result, Err(IntegerPureSubstitutionError::WorkLimitExceeded));
    }
}
