use super::*;

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

pub(in crate::kernel) fn substitute_bitvector_variable_in_proposition(
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
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition,
        } => Proposition::CWhileInvariantRule {
            state: substitute_bitvector_variable_in_c_state(state, from, to),
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            body: substitute_bitvector_variable_in_c_statement(body, from, to),
            preserved: preserved
                .iter()
                .map(|proposition| {
                    substitute_bitvector_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            postcondition: Box::new(substitute_bitvector_variable_in_proposition(
                postcondition,
                from,
                to,
            )),
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
        Proposition::CWhileInvariantRule {
            invariant,
            preserved,
            postcondition,
            ..
        } => {
            for proposition in invariant.iter().chain(preserved) {
                collect_proposition_bound_variables(proposition, variables);
            }
            collect_proposition_bound_variables(postcondition, variables);
        }
    }
}

fn collect_term_bound_variables(term: &Term, variables: &mut BTreeSet<Variable>) {
    match term {
        Term::Condition(condition) => collect_condition_bound_variables(condition, variables),
        Term::Bitvector32(bits) => collect_bitvector_bound_variables(bits, variables),
        Term::PointerOffset(offset) => collect_pointer_offset_bound_variables(offset, variables),
        Term::CValue(value) => collect_c_value_bound_variables(value, variables),
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

fn collect_c_value_bound_variables(value: &CValue, variables: &mut BTreeSet<Variable>) {
    match value {
        CValue::Int16(bits)
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

fn collect_c_statement_bound_variables(statement: &CStatement, variables: &mut BTreeSet<Variable>) {
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

fn collect_c_state_bound_variables(state: &CState, variables: &mut BTreeSet<Variable>) {
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
        for argument in &population.arguments {
            collect_c_value_bound_variables(argument, variables);
        }
        collect_bitvector_bound_variables(&population.count, variables);
    }
}

fn collect_statement_outcome_bound_variables(
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
    match resource {
        CResourceSpec::Quantified { quantity, resource } => {
            collect_c_expression_bound_variables(quantity, variables);
            collect_c_resource_spec_bound_variables(resource, variables);
        }
        CResourceSpec::ViewMemory(segment) | CResourceSpec::OwnMemory(segment) => {
            collect_c_memory_segment_bound_variables(segment, variables)
        }
        CResourceSpec::Composite { arguments, .. } | CResourceSpec::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_expression_bound_variables(argument, variables);
            }
        }
    }
}

fn collect_c_function_bound_variables(function: &CFunction, variables: &mut BTreeSet<Variable>) {
    for resource in function.resource_requires() {
        collect_c_resource_spec_bound_variables(resource, variables);
    }
    for resource in function.resource_ensures() {
        collect_c_resource_spec_bound_variables(resource, variables);
    }
    for proposition in function.contract_requires() {
        collect_spec_proposition_bound_variables(proposition, variables);
    }
    for proposition in function.contract_ensures() {
        collect_spec_proposition_bound_variables(proposition, variables);
    }
    for segment in function.contract_mutable() {
        collect_c_memory_segment_bound_variables(segment, variables);
    }
    collect_c_statement_bound_variables(function.body(), variables);
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
        CResource::Memory(range) => {
            collect_pointer_bound_variables(&range.base, variables);
            collect_bitvector_bound_variables(&range.start, variables);
            collect_bitvector_bound_variables(&range.end, variables);
        }
        CResource::Composite { arguments, .. } | CResource::Token { arguments, .. } => {
            for argument in arguments {
                collect_c_value_bound_variables(argument, variables);
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
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            // Memory snapshots are immutable kernel values; their free
            // variable collector remains the source of truth for snapshot
            // contents, while the pointer can contain nested fold terms.
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_offset_bound_variables(&pointer.offset, variables);
        }
        Bitvector32Term::Int64Constant(_) | Bitvector32Term::UInt64Constant(_) => {}
        Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
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

fn collect_condition_bound_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
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
        Term::PointerOffset(offset) => Term::PointerOffset(
            substitute_bitvector_variable_in_pointer_offset(offset, from, to),
        ),
        Term::CValue(value) => {
            Term::CValue(substitute_bitvector_variable_in_c_value(value, from, to))
        }
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
        } => CExpression::Cast {
            expression: Box::new(substitute_bitvector_variable_in_c_expression(
                expression, from, to,
            )),
            target_type: *target_type,
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
        } => CExpression::TypedLoad {
            pointer: Box::new(substitute_bitvector_variable_in_c_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
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
        } => CStatement::Declare {
            name: name.clone(),
            c_type: *c_type,
            volatile: *volatile,
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
        } => CStatement::TypedStore {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
            value: substitute_bitvector_variable_in_c_expression(value, from, to),
            value_type: *value_type,
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
            body,
            do_while,
        } => CStatement::While {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
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

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecExpression {
    match expression {
        SpecExpression::Value(value) => {
            SpecExpression::Value(substitute_bitvector_variable_in_c_value(value, from, to))
        }
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
        SpecExpression::PureFunctionApplication { name, arguments } => {
            SpecExpression::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_bitvector_variable_in_spec_expression(argument, from, to)
                    })
                    .collect(),
            }
        }
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

pub(in crate::kernel) fn substitute_bitvector_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &Bitvector32Term,
) -> SpecProposition {
    match proposition {
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
                    } => CLocalBinding::Object {
                        value: substitute_bitvector_variable_in_c_value(value, from, to),
                        c_type: *c_type,
                        slot: slot.clone(),
                        volatile: *volatile,
                    },
                    CLocalBinding::UninitializedObject {
                        c_type,
                        slot,
                        volatile,
                    } => CLocalBinding::UninitializedObject {
                        c_type: *c_type,
                        slot: slot.clone(),
                        volatile: *volatile,
                    },
                    CLocalBinding::GlobalObject {
                        c_type,
                        slot,
                        volatile,
                    } => CLocalBinding::GlobalObject {
                        c_type: *c_type,
                        slot: slot.clone(),
                        volatile: *volatile,
                    },
                    CLocalBinding::ArrayObject {
                        element_type,
                        length,
                        slot,
                    } => CLocalBinding::ArrayObject {
                        element_type: *element_type,
                        length: *length,
                        slot: slot.clone(),
                    },
                    CLocalBinding::AggregateObject { layout, slot } => {
                        CLocalBinding::AggregateObject {
                            layout: layout.clone(),
                            slot: slot.clone(),
                        }
                    }
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
        resources: substitute_bitvector_variable_in_resource_context(&state.resources, from, to),
        next_local_frame: state.next_local_frame,
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
                            substitute_bitvector_variable_in_c_value(argument, from, to)
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
        CResource::Memory(range) => CResource::Memory(
            substitute_bitvector_variable_in_c_memory_range(range, from, to),
        ),
        CResource::Composite { name, arguments } => CResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_value(argument, from, to))
                .collect(),
        },
        CResource::Token { name, arguments } => CResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_value(argument, from, to))
                .collect(),
        },
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_c_function(
    function: &CFunction,
    from: Variable,
    to: &Bitvector32Term,
) -> CFunction {
    CFunction {
        return_type: function.return_type,
        name: function.name.clone(),
        parameters: function.parameters.clone(),
        body: substitute_bitvector_variable_in_c_statement(function.body(), from, to),
        source_body: substitute_bitvector_variable_in_c_statement(function.source_body(), from, to),
        return_aggregate_layout: function.return_aggregate_layout.clone(),
        resource_requires: function
            .resource_requires()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
            .collect(),
        resource_ensures: function
            .resource_ensures()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
            .collect(),
        resource_constructors: function
            .resource_constructors()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource_spec(resource, from, to))
            .collect(),
        contract_requires: function
            .contract_requires
            .iter()
            .map(|proposition| {
                substitute_bitvector_variable_in_spec_proposition(proposition, from, to)
            })
            .collect(),
        contract_ensures: function
            .contract_ensures
            .iter()
            .map(|proposition| {
                substitute_bitvector_variable_in_spec_proposition(proposition, from, to)
            })
            .collect(),
        contract_mutable: function
            .contract_mutable
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
        contract_effect_claim_required: function.contract_effect_claim_required,
        contract_claims: function.contract_claims.clone(),
        opaque_contract_supported: function.opaque_contract_supported,
        composite_resource_definitions: function
            .composite_resource_definitions
            .iter()
            .map(|definition| CCompositeResourceDefinition {
                name: definition.name.clone(),
                parameters: definition.parameters.clone(),
                condition: definition.condition.as_ref().map(|condition| {
                    substitute_bitvector_variable_in_spec_proposition(condition, from, to)
                }),
                recursive: definition.recursive,
                counted_population: definition.counted_population,
                contains: definition
                    .contains
                    .iter()
                    .map(|resource| {
                        substitute_bitvector_variable_in_resource_spec(resource, from, to)
                    })
                    .collect(),
                facts: definition
                    .facts
                    .iter()
                    .map(|fact| substitute_bitvector_variable_in_spec_proposition(fact, from, to))
                    .collect(),
            })
            .collect(),
        predicate_unfoldings: function
            .predicate_unfoldings
            .iter()
            .map(|unfolding| CPredicateUnfolding {
                predicate: substitute_bitvector_variable_in_spec_proposition(
                    &unfolding.predicate,
                    from,
                    to,
                ),
                body: substitute_bitvector_variable_in_spec_proposition(&unfolding.body, from, to),
            })
            .collect(),
        global_variables: function.global_variables.clone(),
        global_arrays: function.global_arrays.clone(),
        static_variables: function.static_variables.clone(),
        static_arrays: function.static_arrays.clone(),
        string_literals: function.string_literals.clone(),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_resource_spec(
    resource: &CResourceSpec,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceSpec {
    match resource {
        CResourceSpec::Quantified { quantity, resource } => CResourceSpec::Quantified {
            quantity: substitute_bitvector_variable_in_c_expression(quantity, from, to),
            resource: Box::new(substitute_bitvector_variable_in_resource_spec(
                resource, from, to,
            )),
        },
        CResourceSpec::ViewMemory(segment) => CResourceSpec::ViewMemory(CMemorySegment {
            base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
            start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
            end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
            element_width: segment.element_width,
            guard: segment
                .guard
                .as_ref()
                .map(|guard| substitute_bitvector_variable_in_spec_proposition(guard, from, to)),
        }),
        CResourceSpec::OwnMemory(segment) => CResourceSpec::OwnMemory(CMemorySegment {
            base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
            start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
            end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
            element_width: segment.element_width,
            guard: segment
                .guard
                .as_ref()
                .map(|guard| substitute_bitvector_variable_in_spec_proposition(guard, from, to)),
        }),
        CResourceSpec::Composite {
            access,
            name,
            arguments,
            parameter_types,
        } => CResourceSpec::Composite {
            access: *access,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_bitvector_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
        CResourceSpec::Token {
            access,
            name,
            arguments,
            parameter_types,
        } => CResourceSpec::Token {
            access: *access,
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

pub(in crate::kernel) fn substitute_bitvector_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Bitvector32Term,
) -> ConditionTerm {
    match condition {
        ConditionTerm::Constant(value) => ConditionTerm::Constant(*value),
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

pub(in crate::kernel) fn substitute_bitvector_variable(
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
        Bitvector32Term::MemoryLoad(memory, pointer) => Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(substitute_bitvector_variable_in_memory(
                memory, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_pointer(pointer, from, to)),
        ),
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
        ),
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
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition,
        } => Proposition::CWhileInvariantRule {
            state: substitute_pointer_variable_in_c_state(state, from, to),
            condition: substitute_pointer_variable_in_c_expression(condition, from, to),
            invariant: invariant
                .iter()
                .map(|proposition| {
                    substitute_pointer_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            body: substitute_pointer_variable_in_c_statement(body, from, to),
            preserved: preserved
                .iter()
                .map(|proposition| {
                    substitute_pointer_variable_in_proposition(proposition, from, to)
                })
                .collect(),
            postcondition: Box::new(substitute_pointer_variable_in_proposition(
                postcondition,
                from,
                to,
            )),
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
        Term::Bitvector32(_) | Term::PointerOffset(_) => term.clone(),
        Term::CValue(value) => {
            Term::CValue(substitute_pointer_variable_in_c_value(value, from, to))
        }
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

fn substitute_pointer_variable_in_condition(
    condition: &ConditionTerm,
    from: Variable,
    to: &Pointer,
) -> ConditionTerm {
    match condition {
        ConditionTerm::PointerEqual(left, right) => ConditionTerm::pointer_equal(
            substitute_pointer_variable_in_pointer(left, from, to),
            substitute_pointer_variable_in_pointer(right, from, to),
        ),
        condition => condition.clone(),
    }
}

fn substitute_pointer_variable_in_c_value(value: &CValue, from: Variable, to: &Pointer) -> CValue {
    match value {
        CValue::Pointer(pointer) => CValue::typed_pointer(
            substitute_pointer_variable_in_pointer(pointer.pointer(), from, to),
            pointer.c_type(),
        ),
        CValue::Void
        | CValue::Int16(_)
        | CValue::Int32(_)
        | CValue::UInt8(_)
        | CValue::UInt16(_)
        | CValue::UInt32(_)
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => value.clone(),
    }
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
        } => CExpression::Cast {
            expression: Box::new(substitute_pointer_variable_in_c_expression(
                expression, from, to,
            )),
            target_type: *target_type,
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
        } => CExpression::TypedLoad {
            pointer: Box::new(substitute_pointer_variable_in_c_expression(
                pointer, from, to,
            )),
            value_type: *value_type,
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
        } => CStatement::TypedStore {
            pointer: substitute_pointer_variable_in_c_expression(pointer, from, to),
            value: substitute_pointer_variable_in_c_expression(value, from, to),
            value_type: *value_type,
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
            body,
            do_while,
        } => CStatement::While {
            condition: substitute_pointer_variable_in_c_expression(condition, from, to),
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
                    } => CLocalBinding::Object {
                        value: substitute_pointer_variable_in_c_value(value, from, to),
                        c_type: *c_type,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        volatile: *volatile,
                    },
                    CLocalBinding::UninitializedObject {
                        c_type,
                        slot,
                        volatile,
                    } => CLocalBinding::UninitializedObject {
                        c_type: *c_type,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        volatile: *volatile,
                    },
                    CLocalBinding::GlobalObject {
                        c_type,
                        slot,
                        volatile,
                    } => CLocalBinding::GlobalObject {
                        c_type: *c_type,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        volatile: *volatile,
                    },
                    CLocalBinding::ArrayObject {
                        element_type,
                        length,
                        slot,
                    } => CLocalBinding::ArrayObject {
                        element_type: *element_type,
                        length: *length,
                        slot: substitute_pointer_variable_in_pointer(slot, from, to),
                    },
                    CLocalBinding::AggregateObject { layout, slot } => {
                        CLocalBinding::AggregateObject {
                            layout: layout.clone(),
                            slot: substitute_pointer_variable_in_pointer(slot, from, to),
                        }
                    }
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
        resources: substitute_pointer_variable_in_resource_context(&state.resources, from, to),
        next_local_frame: state.next_local_frame,
        counted_populations: std::sync::Arc::new(
            state
                .counted_populations
                .iter()
                .map(|population| CCountedPopulation {
                    name: population.name.clone(),
                    arguments: population
                        .arguments
                        .iter()
                        .map(|argument| substitute_pointer_variable_in_c_value(argument, from, to))
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
        CResource::Memory(range) => CResource::Memory(
            substitute_pointer_variable_in_c_memory_range(range, from, to),
        ),
        CResource::Composite { name, arguments } => CResource::Composite {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_value(argument, from, to))
                .collect(),
        },
        CResource::Token { name, arguments } => CResource::Token {
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_value(argument, from, to))
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

fn substitute_pointer_variable_in_spec_expression(
    expression: &SpecExpression,
    from: Variable,
    to: &Pointer,
) -> SpecExpression {
    match expression {
        SpecExpression::Value(value) => {
            SpecExpression::Value(substitute_pointer_variable_in_c_value(value, from, to))
        }
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
        SpecExpression::PureFunctionApplication { name, arguments } => {
            SpecExpression::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        substitute_pointer_variable_in_spec_expression(argument, from, to)
                    })
                    .collect(),
            }
        }
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

fn substitute_pointer_variable_in_spec_proposition(
    proposition: &SpecProposition,
    from: Variable,
    to: &Pointer,
) -> SpecProposition {
    match proposition {
        SpecProposition::Comparison {
            left,
            operator,
            right,
        } => SpecProposition::Comparison {
            left: substitute_pointer_variable_in_spec_expression(left, from, to),
            operator: *operator,
            right: substitute_pointer_variable_in_spec_expression(right, from, to),
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
    CFunction {
        return_type: function.return_type,
        name: function.name.clone(),
        parameters: function.parameters.clone(),
        body: substitute_pointer_variable_in_c_statement(function.body(), from, to),
        source_body: substitute_pointer_variable_in_c_statement(function.source_body(), from, to),
        return_aggregate_layout: function.return_aggregate_layout.clone(),
        resource_requires: function
            .resource_requires()
            .iter()
            .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
            .collect(),
        resource_ensures: function
            .resource_ensures()
            .iter()
            .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
            .collect(),
        resource_constructors: function
            .resource_constructors()
            .iter()
            .map(|resource| substitute_pointer_variable_in_resource_spec(resource, from, to))
            .collect(),
        contract_requires: function
            .contract_requires
            .iter()
            .map(|proposition| {
                substitute_pointer_variable_in_spec_proposition(proposition, from, to)
            })
            .collect(),
        contract_ensures: function
            .contract_ensures
            .iter()
            .map(|proposition| {
                substitute_pointer_variable_in_spec_proposition(proposition, from, to)
            })
            .collect(),
        contract_mutable: function
            .contract_mutable
            .iter()
            .map(|segment| CMemorySegment {
                base: substitute_pointer_variable_in_c_expression(&segment.base, from, to),
                start: substitute_pointer_variable_in_c_expression(&segment.start, from, to),
                end: substitute_pointer_variable_in_c_expression(&segment.end, from, to),
                element_width: segment.element_width,
                guard: segment
                    .guard
                    .as_ref()
                    .map(|guard| substitute_pointer_variable_in_spec_proposition(guard, from, to)),
            })
            .collect(),
        contract_effect_claim_required: function.contract_effect_claim_required,
        contract_claims: function.contract_claims.clone(),
        opaque_contract_supported: function.opaque_contract_supported,
        composite_resource_definitions: function
            .composite_resource_definitions
            .iter()
            .map(|definition| CCompositeResourceDefinition {
                name: definition.name.clone(),
                parameters: definition.parameters.clone(),
                condition: definition.condition.as_ref().map(|condition| {
                    substitute_pointer_variable_in_spec_proposition(condition, from, to)
                }),
                recursive: definition.recursive,
                counted_population: definition.counted_population,
                contains: definition
                    .contains
                    .iter()
                    .map(|resource| {
                        substitute_pointer_variable_in_resource_spec(resource, from, to)
                    })
                    .collect(),
                facts: definition
                    .facts
                    .iter()
                    .map(|fact| substitute_pointer_variable_in_spec_proposition(fact, from, to))
                    .collect(),
            })
            .collect(),
        predicate_unfoldings: function
            .predicate_unfoldings
            .iter()
            .map(|unfolding| CPredicateUnfolding {
                predicate: substitute_pointer_variable_in_spec_proposition(
                    &unfolding.predicate,
                    from,
                    to,
                ),
                body: substitute_pointer_variable_in_spec_proposition(&unfolding.body, from, to),
            })
            .collect(),
        global_variables: function.global_variables.clone(),
        global_arrays: function.global_arrays.clone(),
        static_variables: function.static_variables.clone(),
        static_arrays: function.static_arrays.clone(),
        string_literals: function.string_literals.clone(),
    }
}

fn substitute_pointer_variable_in_resource_spec(
    resource: &CResourceSpec,
    from: Variable,
    to: &Pointer,
) -> CResourceSpec {
    match resource {
        CResourceSpec::Quantified { quantity, resource } => CResourceSpec::Quantified {
            quantity: substitute_pointer_variable_in_c_expression(quantity, from, to),
            resource: Box::new(substitute_pointer_variable_in_resource_spec(
                resource, from, to,
            )),
        },
        CResourceSpec::ViewMemory(segment) => CResourceSpec::ViewMemory(CMemorySegment {
            base: substitute_pointer_variable_in_c_expression(&segment.base, from, to),
            start: substitute_pointer_variable_in_c_expression(&segment.start, from, to),
            end: substitute_pointer_variable_in_c_expression(&segment.end, from, to),
            element_width: segment.element_width,
            guard: segment
                .guard
                .as_ref()
                .map(|guard| substitute_pointer_variable_in_spec_proposition(guard, from, to)),
        }),
        CResourceSpec::OwnMemory(segment) => CResourceSpec::OwnMemory(CMemorySegment {
            base: substitute_pointer_variable_in_c_expression(&segment.base, from, to),
            start: substitute_pointer_variable_in_c_expression(&segment.start, from, to),
            end: substitute_pointer_variable_in_c_expression(&segment.end, from, to),
            element_width: segment.element_width,
            guard: segment
                .guard
                .as_ref()
                .map(|guard| substitute_pointer_variable_in_spec_proposition(guard, from, to)),
        }),
        CResourceSpec::Composite {
            access,
            name,
            arguments,
            parameter_types,
        } => CResourceSpec::Composite {
            access: *access,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_pointer_variable_in_c_expression(argument, from, to))
                .collect(),
            parameter_types: parameter_types.clone(),
        },
        CResourceSpec::Token {
            access,
            name,
            arguments,
            parameter_types,
        } => CResourceSpec::Token {
            access: *access,
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
