use super::*;

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
        Proposition::CHeapLifetimeRetired {
            before,
            after,
            allocation_base,
            bytes,
        } => Proposition::CHeapLifetimeRetired {
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
    let mut variables = VerificationVariableGenerator::fresh_for(0, reserved);
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
        _ => {}
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
        CStatement::Declare { name, c_type } => CStatement::Declare {
            name: name.clone(),
            c_type: *c_type,
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
        CStatement::HeapAllocate { target, bytes } => CStatement::HeapAllocate {
            target: target.clone(),
            bytes: substitute_bitvector_variable_in_c_expression(bytes, from, to),
        },
        CStatement::HeapFree { pointer } => CStatement::HeapFree {
            pointer: substitute_bitvector_variable_in_c_expression(pointer, from, to),
        },
        CStatement::Assert { condition, label } => CStatement::Assert {
            condition: substitute_bitvector_variable_in_c_expression(condition, from, to),
            label: label.clone(),
        },
        CStatement::Seq(first, second) => CStatement::Seq(
            Box::new(substitute_bitvector_variable_in_c_statement(
                first, from, to,
            )),
            Box::new(substitute_bitvector_variable_in_c_statement(
                second, from, to,
            )),
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
            body: Box::new(substitute_bitvector_variable_in_c_statement(body, from, to)),
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
        SpecResource::Memory { base, start, end } => SpecResource::Memory {
            base: substitute_bitvector_variable_in_spec_expression(base, from, to),
            start: substitute_bitvector_variable_in_spec_expression(start, from, to),
            end: substitute_bitvector_variable_in_spec_expression(end, from, to),
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
    let bindings = state
        .locals
        .bindings
        .iter()
        .map(|(name, binding)| {
            let binding = match binding {
                CLocalBinding::Object { value, c_type } => CLocalBinding::Object {
                    value: substitute_bitvector_variable_in_c_value(value, from, to),
                    c_type: *c_type,
                },
                CLocalBinding::UninitializedObject { c_type } => {
                    CLocalBinding::UninitializedObject { c_type: *c_type }
                }
                CLocalBinding::ArrayObject {
                    element_type,
                    length,
                } => CLocalBinding::ArrayObject {
                    element_type: *element_type,
                    length: *length,
                },
            };
            (name.clone(), binding)
        })
        .collect();
    CState {
        locals: CLocalEnvironment { bindings },
        memory: substitute_bitvector_variable_in_memory(&state.memory, from, to),
        resources: substitute_bitvector_variable_in_resource_context(&state.resources, from, to),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_resource_context(
    resources: &ResourceContext,
    from: Variable,
    to: &Bitvector32Term,
) -> ResourceContext {
    ResourceContext {
        facts: resources
            .facts()
            .iter()
            .map(|resource| substitute_bitvector_variable_in_resource(resource, from, to))
            .collect(),
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_resource(
    resource: &CResourceFact,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceFact {
    match resource {
        CResourceFact::Own(resource) => CResourceFact::Own(
            substitute_bitvector_variable_in_c_resource(resource, from, to),
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
                guard: segment.guard.as_ref().map(|guard| {
                    substitute_bitvector_variable_in_spec_proposition(guard, from, to)
                }),
            })
            .collect(),
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
    }
}

pub(in crate::kernel) fn substitute_bitvector_variable_in_resource_spec(
    resource: &CResourceSpec,
    from: Variable,
    to: &Bitvector32Term,
) -> CResourceSpec {
    match resource {
        CResourceSpec::Read(segment) => CResourceSpec::Read(CMemorySegment {
            base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
            start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
            end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
            guard: segment
                .guard
                .as_ref()
                .map(|guard| substitute_bitvector_variable_in_spec_proposition(guard, from, to)),
        }),
        CResourceSpec::Write(segment) => CResourceSpec::Write(CMemorySegment {
            base: substitute_bitvector_variable_in_c_expression(&segment.base, from, to),
            start: substitute_bitvector_variable_in_c_expression(&segment.start, from, to),
            end: substitute_bitvector_variable_in_c_expression(&segment.end, from, to),
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
    CMemoryRange {
        base: substitute_bitvector_variable_in_pointer(&range.base, from, to),
        start: substitute_bitvector_variable(&range.start, from, to),
        end: substitute_bitvector_variable(&range.end, from, to),
    }
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

pub(in crate::kernel) fn substitute_bitvector_variable(
    term: &Bitvector32Term,
    from: Variable,
    to: &Bitvector32Term,
) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(*value),
        Bitvector32Term::Variable(variable) if *variable == from => to.clone(),
        Bitvector32Term::Variable(variable) => Bitvector32Term::Variable(*variable),
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
        Bitvector32Term::Remainder(left, right) => Bitvector32Term::remainder(
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
            let body = if *accumulator == from || *item == from {
                body.as_ref().clone()
            } else {
                substitute_bitvector_variable(body, from, to)
            };
            Bitvector32Term::range_fold(
                substitute_bitvector_variable(start, from, to),
                substitute_bitvector_variable(end, from, to),
                substitute_bitvector_variable(initial, from, to),
                *accumulator,
                *item,
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
    let cells = memory
        .cells
        .iter()
        .map(|(pointer, value)| {
            (
                substitute_bitvector_variable_in_pointer(pointer, from, to),
                substitute_bitvector_variable_in_c_value(value, from, to),
            )
        })
        .collect();
    CMemory {
        blocks: memory
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
        cells,
        heap: Box::new(CHeapMemory {
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
            retired_allocations: memory
                .heap
                .retired_allocations
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
        CValue::Int32(bits) => int32(substitute_bitvector_variable(bits, from, to)),
        CValue::UInt8(bits) => uint8(substitute_bitvector_variable(bits, from, to)),
        CValue::Pointer(pointer) => {
            CValue::Pointer(substitute_bitvector_variable_in_pointer(pointer, from, to))
        }
    }
}
