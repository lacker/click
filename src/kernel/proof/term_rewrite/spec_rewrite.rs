use super::*;
use crate::kernel::*;
use std::collections::BTreeSet;

/// Failure from the checked Spec substitution pass.  A resource rewrite must
/// refuse the complete proposition when this happens; returning a partially
/// rewritten clone would leave the arm binding in the proof object.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SpecRewriteError {
    UnsupportedCarrier,
    WorkLimitExceeded,
}

/// Feed the Spec-shaped nodes into the shared carrier collector in
/// `term_rewrite.rs`.  Spec binders have a few name-based forms, but every
/// proof-relevant numeric identity is already represented by one of the
/// typed carrier terms that the shared collector understands.  Keeping this
/// adapter separate from the rewrite walk makes source reservation complete
/// before the first binder is freshened and keeps registered-load handling in
/// one place.
fn collect_spec_proposition_carriers(
    proposition: &SpecProposition,
    variables: &mut CarrierVariables,
    integer_seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match proposition {
        SpecProposition::IntegerComparison { left, right, .. } => {
            collect_spec_integer_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_integer_carriers(right, variables, integer_seen);
        }
        SpecProposition::AlgebraicComparison { left, right, .. } => {
            collect_spec_algebraic_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_algebraic_carriers(right, variables, integer_seen);
        }
        SpecProposition::SequenceMembership { element, sequence } => {
            collect_spec_expression_carriers(element, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_sequence_carriers(sequence, variables, integer_seen);
        }
        SpecProposition::SequenceComparison { left, right, .. } => {
            collect_spec_sequence_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_sequence_carriers(right, variables, integer_seen);
        }
        SpecProposition::Comparison { left, right, .. } => {
            collect_spec_expression_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(right, variables, integer_seen);
        }
        SpecProposition::FloatClassification { expression, .. }
        | SpecProposition::Defined(expression) => {
            collect_spec_expression_carriers(expression, variables, integer_seen);
        }
        SpecProposition::And(left, right)
        | SpecProposition::Or(left, right)
        | SpecProposition::Implies(left, right) => {
            collect_spec_proposition_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_proposition_carriers(right, variables, integer_seen);
        }
        SpecProposition::Not(body) => {
            collect_spec_proposition_carriers(body, variables, integer_seen);
        }
        SpecProposition::ForAllInt32 { variable, body, .. }
        | SpecProposition::ExistsInt32 { variable, body, .. }
        | SpecProposition::ForAllPointer { variable, body, .. }
        | SpecProposition::ExistsPointer { variable, body, .. } => {
            variables.c.insert(*variable);
            collect_spec_proposition_carriers(body, variables, integer_seen);
        }
        SpecProposition::ForAllInteger { variable, body, .. }
        | SpecProposition::ExistsInteger { variable, body, .. } => {
            variables.integer.insert(*variable);
            collect_spec_proposition_carriers(body, variables, integer_seen);
        }
        SpecProposition::Predicate { arguments, .. } => {
            for argument in arguments {
                if variables.exhausted() {
                    return;
                }
                match argument {
                    SpecPredicateArgument::Value(value) => {
                        collect_spec_expression_carriers(value, variables, integer_seen)
                    }
                    SpecPredicateArgument::ArrayRef { pointer, .. } => {
                        collect_spec_expression_carriers(pointer, variables, integer_seen)
                    }
                }
            }
        }
        SpecProposition::ResourceSeparate { left, right }
        | SpecProposition::ResourceContains {
            parent: left,
            child: right,
        } => {
            collect_spec_resource_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_resource_carriers(right, variables, integer_seen);
        }
        SpecProposition::MemoryLoadable {
            base, start, end, ..
        } => {
            collect_spec_expression_carriers(base, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(start, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(end, variables, integer_seen);
        }
    }
}

fn collect_spec_integer_carriers(
    expression: &SpecIntegerExpression,
    variables: &mut CarrierVariables,
    integer_seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match expression {
        SpecIntegerExpression::ResourceField(projection) => {
            variables.c.insert(projection.identity);
        }
        SpecIntegerExpression::Term(term) => {
            collect_integer_carriers(term, variables, integer_seen)
        }
        SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if variables.exhausted() {
                    return;
                }
                collect_spec_argument_carriers(argument, variables, integer_seen);
            }
        }
        SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_spec_algebraic_carriers(scrutinee, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                for (binding_type, binding_variable) in
                    arm.binding_types.iter().zip(&arm.binding_variables)
                {
                    if variables.exhausted() {
                        return;
                    }
                    if let Some(variable) = binding_variable {
                        match binding_type {
                            AlgebraicValueType::Integer => {
                                variables.integer.insert(*variable);
                            }
                            AlgebraicValueType::C(_) => {
                                variables.c.insert(*variable);
                            }
                            AlgebraicValueType::Algebraic { .. }
                            | AlgebraicValueType::Parameter(_) => {
                                variables.algebraic.insert(*variable);
                            }
                        }
                    }
                }
                collect_spec_integer_carriers(&arm.body, variables, integer_seen);
            }
        }
        SpecIntegerExpression::FromMachine(value) => {
            collect_spec_expression_carriers(value, variables, integer_seen)
        }
        SpecIntegerExpression::Negate(value) => {
            collect_spec_integer_carriers(value, variables, integer_seen)
        }
        SpecIntegerExpression::Add(left, right)
        | SpecIntegerExpression::Subtract(left, right)
        | SpecIntegerExpression::Multiply(left, right) => {
            collect_spec_integer_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_integer_carriers(right, variables, integer_seen);
        }
        SpecIntegerExpression::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                SpecIntegerRangeFoldIndex::Int32 { start, end } => {
                    collect_spec_expression_carriers(start, variables, integer_seen);
                    if variables.exhausted() {
                        return;
                    }
                    collect_spec_expression_carriers(end, variables, integer_seen);
                }
                SpecIntegerRangeFoldIndex::Integer { start, end } => {
                    collect_spec_integer_carriers(start, variables, integer_seen);
                    if variables.exhausted() {
                        return;
                    }
                    collect_spec_integer_carriers(end, variables, integer_seen);
                }
            }
            if variables.exhausted() {
                return;
            }
            collect_spec_integer_carriers(initial, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_integer_carriers(body, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            variables.integer.insert(*accumulator);
            match index {
                SpecIntegerRangeFoldIndex::Int32 { .. } => {
                    variables.c.insert(*item);
                }
                SpecIntegerRangeFoldIndex::Integer { .. } => {
                    variables.integer.insert(*item);
                }
            }
        }
    }
}

fn collect_spec_expression_carriers(
    expression: &SpecExpression,
    variables: &mut CarrierVariables,
    integer_seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match expression {
        SpecExpression::Value(value) => collect_c_value_carriers(value, variables),
        SpecExpression::IntegerToMachine { value, .. } => {
            collect_spec_integer_carriers(value, variables, integer_seen)
        }
        SpecExpression::ResourceField { projection, .. } => {
            variables.c.insert(projection.identity);
        }
        SpecExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_spec_algebraic_carriers(scrutinee, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                if variables.exhausted() {
                    return;
                }
                collect_spec_expression_carriers(&arm.body, variables, integer_seen);
            }
        }
        SpecExpression::CExpression(expression) => {
            collect_spec_c_expression_carriers(expression, variables)
        }
        SpecExpression::CountedResourceCount { arguments, .. } => {
            for argument in arguments.iter().flatten() {
                if variables.exhausted() {
                    return;
                }
                collect_spec_expression_carriers(argument, variables, integer_seen);
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
            collect_spec_expression_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(right, variables, integer_seen);
        }
        SpecExpression::BitwiseNot(value) | SpecExpression::Cast(value, _) => {
            collect_spec_expression_carriers(value, variables, integer_seen)
        }
        SpecExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_spec_proposition_carriers(condition, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(then_branch, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(else_branch, variables, integer_seen);
        }
        SpecExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_spec_expression_carriers(start, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(end, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(initial, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(body, variables, integer_seen);
        }
        SpecExpression::Let { value, body, .. } => {
            collect_spec_expression_carriers(value, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(body, variables, integer_seen);
        }
        SpecExpression::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if variables.exhausted() {
                    return;
                }
                collect_spec_argument_carriers(argument, variables, integer_seen);
            }
        }
        SpecExpression::LoopEntrySnapshot(value) => {
            collect_spec_expression_carriers(value, variables, integer_seen)
        }
        SpecExpression::PointerOffset {
            pointer, elements, ..
        } => {
            collect_spec_expression_carriers(pointer, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(elements, variables, integer_seen);
        }
        SpecExpression::MemoryLoad { pointer, .. } => {
            collect_spec_expression_carriers(pointer, variables, integer_seen)
        }
    }
}

fn collect_spec_c_expression_carriers(expression: &CExpression, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match expression {
        CExpression::Value(value) => collect_c_value_carriers(value, variables),
        CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. }
        | CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. }
        | CExpression::AddressOf(expression)
        | CExpression::Not(expression)
        | CExpression::Load(expression)
        | CExpression::BitwiseNot(expression) => {
            collect_spec_c_expression_carriers(expression, variables)
        }
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_spec_c_expression_carriers(pointer, variables)
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_spec_c_expression_carriers(condition, variables);
            if variables.exhausted() {
                return;
            }
            collect_spec_c_expression_carriers(then_branch, variables);
            if variables.exhausted() {
                return;
            }
            collect_spec_c_expression_carriers(else_branch, variables);
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
            collect_spec_c_expression_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_spec_c_expression_carriers(right, variables);
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_spec_c_expression_carriers(pointer, variables)
        }
    }
}

fn collect_spec_algebraic_carriers(
    expression: &SpecAlgebraicExpression,
    variables: &mut CarrierVariables,
    integer_seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match &expression.node {
        SpecAlgebraicExpressionNode::Variable(variable) => {
            variables.algebraic.insert(*variable);
        }
        SpecAlgebraicExpressionNode::Binding(_) => {}
        SpecAlgebraicExpressionNode::ResourceField(projection) => {
            variables.c.insert(projection.identity);
        }
        SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
            for field in fields {
                if variables.exhausted() {
                    return;
                }
                match field {
                    SpecAlgebraicValue::C(value) => {
                        collect_spec_expression_carriers(value, variables, integer_seen)
                    }
                    SpecAlgebraicValue::Integer(value) => {
                        collect_spec_integer_carriers(value, variables, integer_seen)
                    }
                    SpecAlgebraicValue::Algebraic(value) => {
                        collect_spec_algebraic_carriers(value, variables, integer_seen)
                    }
                }
            }
        }
        SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
            collect_spec_algebraic_carriers(scrutinee, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                collect_spec_algebraic_carriers(&arm.body, variables, integer_seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if variables.exhausted() {
                    return;
                }
                collect_spec_argument_carriers(argument, variables, integer_seen);
            }
        }
    }
}

fn collect_spec_argument_carriers(
    argument: &SpecPureFunctionArgument,
    variables: &mut CarrierVariables,
    integer_seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match argument {
        SpecPureFunctionArgument::Value(value) => {
            collect_spec_expression_carriers(value, variables, integer_seen)
        }
        SpecPureFunctionArgument::Integer(value) => {
            collect_spec_integer_carriers(value, variables, integer_seen)
        }
        SpecPureFunctionArgument::Algebraic(value) => {
            collect_spec_algebraic_carriers(value, variables, integer_seen)
        }
        SpecPureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_spec_expression_carriers(pointer, variables, integer_seen)
        }
    }
}

fn collect_spec_sequence_carriers(
    sequence: &SpecSequenceExpression,
    variables: &mut CarrierVariables,
    integer_seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match sequence {
        SpecSequenceExpression::Literal(values) => {
            for value in values {
                if variables.exhausted() {
                    return;
                }
                collect_spec_expression_carriers(value, variables, integer_seen);
            }
        }
        SpecSequenceExpression::Concat(left, right) => {
            collect_spec_sequence_carriers(left, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_sequence_carriers(right, variables, integer_seen);
        }
    }
}

fn collect_spec_resource_carriers(
    resource: &SpecResource,
    variables: &mut CarrierVariables,
    integer_seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    let arguments = match resource {
        SpecResource::Memory {
            base, start, end, ..
        } => {
            collect_spec_expression_carriers(base, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(start, variables, integer_seen);
            if variables.exhausted() {
                return;
            }
            collect_spec_expression_carriers(end, variables, integer_seen);
            return;
        }
        SpecResource::Composite { arguments, .. } | SpecResource::Token { arguments, .. } => {
            arguments
        }
    };
    for argument in arguments {
        if variables.exhausted() {
            return;
        }
        collect_spec_expression_carriers(argument, variables, integer_seen);
    }
}

impl<'a> TermRewrite<'a> {
    /// Rewrite a complete specification proposition with the typed
    /// replacements installed in this walker.  This is intentionally one
    /// entry point for all Spec carriers: resource matching used to rewrite
    /// only `SpecIntegerExpression`, which left Integer occurrences hidden in
    /// machine casts, C comparisons, and function arguments untouched.
    pub(crate) fn spec_proposition(
        &mut self,
        proposition: &SpecProposition,
    ) -> Result<SpecProposition, SpecRewriteError> {
        self.reserve_spec_proposition_sources(std::iter::once(proposition))?;
        let result = self.rewrite_spec_proposition(proposition)?;
        self.spec_status()?;
        Ok(result)
    }

    /// Reserve source identities for a complete batch before rewriting any
    /// member of that batch.  Resource matching reuses one walker for all
    /// selected arm facts, so reserving only the first fact would leave a
    /// later free source identity available for accidental capture.
    pub(crate) fn reserve_spec_proposition_sources<'p, I>(
        &mut self,
        propositions: I,
    ) -> Result<(), SpecRewriteError>
    where
        I: IntoIterator<Item = &'p SpecProposition>,
    {
        self.ensure_replacement_carriers();
        self.reserve_spec_source_variables_once(propositions);
        self.spec_status()
    }

    /// Reserve every source identity before any specification binder can be
    /// freshened.  Resource facts can contain mathematical Integers hidden in
    /// machine casts, C payloads, algebraic fields, and range-fold bodies;
    /// reserving only the first Integer leaf lets a later free source ID be
    /// captured by an earlier fresh binder.  The shared bound-identity
    /// collector also keeps captured snapshots opaque and memoizes shared
    /// Integer DAG nodes.
    fn reserve_spec_source_variables_once<'p, I>(&mut self, propositions: I)
    where
        I: IntoIterator<Item = &'p SpecProposition>,
    {
        if self.source_variables_reserved || self.integer_work_exhausted {
            return;
        }

        // Use the same carrier-aware collector as ordinary checked term
        // rewriting.  In particular, its C walker follows registered load
        // pointers with a scoped cycle set while leaving memory snapshots
        // opaque.  The Spec adapter below only supplies the Spec node
        // structure; it never reimplements the carrier terms themselves.
        let mut variables = self.new_carrier_variables();
        let mut integer_seen = BTreeSet::new();
        for proposition in propositions {
            collect_spec_proposition_carriers(proposition, &mut variables, &mut integer_seen);
            if variables.exhausted() {
                break;
            }
        }
        self.reserve_source_variables(variables);
    }

    fn spec_status(&self) -> Result<(), SpecRewriteError> {
        if self.integer_work_exhausted {
            Err(SpecRewriteError::WorkLimitExceeded)
        } else if self.unsupported_integer_scope {
            Err(SpecRewriteError::UnsupportedCarrier)
        } else {
            Ok(())
        }
    }

    fn spec_visit(&mut self) -> Result<(), SpecRewriteError> {
        self.visit();
        self.spec_status()
    }

    fn rewrite_spec_proposition(
        &mut self,
        proposition: &SpecProposition,
    ) -> Result<SpecProposition, SpecRewriteError> {
        self.spec_visit()?;
        let result = match proposition {
            SpecProposition::IntegerComparison {
                left,
                operator,
                right,
            } => SpecProposition::IntegerComparison {
                left: self.rewrite_spec_integer(left)?,
                operator: *operator,
                right: self.rewrite_spec_integer(right)?,
            },
            SpecProposition::AlgebraicComparison { left, equal, right } => {
                SpecProposition::AlgebraicComparison {
                    left: self.rewrite_spec_algebraic(left)?,
                    equal: *equal,
                    right: self.rewrite_spec_algebraic(right)?,
                }
            }
            SpecProposition::SequenceMembership { element, sequence } => {
                SpecProposition::SequenceMembership {
                    element: self.rewrite_spec_expression(element)?,
                    sequence: self.rewrite_spec_sequence(sequence)?,
                }
            }
            SpecProposition::SequenceComparison { left, equal, right } => {
                SpecProposition::SequenceComparison {
                    left: self.rewrite_spec_sequence(left)?,
                    equal: *equal,
                    right: self.rewrite_spec_sequence(right)?,
                }
            }
            SpecProposition::Comparison {
                left,
                operator,
                right,
            } => SpecProposition::Comparison {
                left: self.rewrite_spec_expression(left)?,
                operator: *operator,
                right: self.rewrite_spec_expression(right)?,
            },
            SpecProposition::FloatClassification {
                expression,
                classification,
            } => SpecProposition::FloatClassification {
                expression: self.rewrite_spec_expression(expression)?,
                classification: *classification,
            },
            SpecProposition::And(left, right) => SpecProposition::And(
                Box::new(self.rewrite_spec_proposition(left)?),
                Box::new(self.rewrite_spec_proposition(right)?),
            ),
            SpecProposition::Or(left, right) => SpecProposition::Or(
                Box::new(self.rewrite_spec_proposition(left)?),
                Box::new(self.rewrite_spec_proposition(right)?),
            ),
            SpecProposition::Not(body) => {
                // Keep a deeply nested unary chain out of the recursive
                // proposition walker.  Besides making this common shape
                // stack-safe, charge each skipped node exactly as the
                // recursive form did.
                let mut not_count = 1;
                let mut inner = body.as_ref();
                while let SpecProposition::Not(next) = inner {
                    self.spec_visit()?;
                    not_count += 1;
                    inner = next.as_ref();
                }
                let mut rewritten = self.rewrite_spec_proposition(inner)?;
                for _ in 0..not_count {
                    rewritten = SpecProposition::Not(Box::new(rewritten));
                }
                rewritten
            }
            SpecProposition::Implies(left, right) => SpecProposition::Implies(
                Box::new(self.rewrite_spec_proposition(left)?),
                Box::new(self.rewrite_spec_proposition(right)?),
            ),
            SpecProposition::ForAllInt32 {
                name,
                variable,
                body,
            } => {
                let (variable, body) =
                    self.with_spec_scope(BindingCarrier::C, *variable, |rewrite| {
                        rewrite.rewrite_spec_proposition(body)
                    })?;
                SpecProposition::ForAllInt32 {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                }
            }
            SpecProposition::ForAllInteger {
                name,
                variable,
                body,
            } => {
                let (variable, body) =
                    self.with_spec_scope(BindingCarrier::Integer, *variable, |rewrite| {
                        rewrite.rewrite_spec_proposition(body)
                    })?;
                SpecProposition::ForAllInteger {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                }
            }
            SpecProposition::ForAllPointer {
                name,
                variable,
                c_type,
                body,
            } => {
                let (variable, body) =
                    self.with_spec_scope(BindingCarrier::C, *variable, |rewrite| {
                        rewrite.rewrite_spec_proposition(body)
                    })?;
                SpecProposition::ForAllPointer {
                    name: name.clone(),
                    variable,
                    c_type: *c_type,
                    body: Box::new(body),
                }
            }
            SpecProposition::ExistsInt32 {
                name,
                variable,
                body,
            } => {
                let (variable, body) =
                    self.with_spec_scope(BindingCarrier::C, *variable, |rewrite| {
                        rewrite.rewrite_spec_proposition(body)
                    })?;
                SpecProposition::ExistsInt32 {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                }
            }
            SpecProposition::ExistsInteger {
                name,
                variable,
                body,
            } => {
                let (variable, body) =
                    self.with_spec_scope(BindingCarrier::Integer, *variable, |rewrite| {
                        rewrite.rewrite_spec_proposition(body)
                    })?;
                SpecProposition::ExistsInteger {
                    name: name.clone(),
                    variable,
                    body: Box::new(body),
                }
            }
            SpecProposition::ExistsPointer {
                name,
                variable,
                c_type,
                body,
            } => {
                let (variable, body) =
                    self.with_spec_scope(BindingCarrier::C, *variable, |rewrite| {
                        rewrite.rewrite_spec_proposition(body)
                    })?;
                SpecProposition::ExistsPointer {
                    name: name.clone(),
                    variable,
                    c_type: *c_type,
                    body: Box::new(body),
                }
            }
            SpecProposition::Predicate { name, arguments } => SpecProposition::Predicate {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.rewrite_spec_predicate_argument(argument))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            SpecProposition::ResourceSeparate { left, right } => {
                SpecProposition::ResourceSeparate {
                    left: self.rewrite_spec_resource(left)?,
                    right: self.rewrite_spec_resource(right)?,
                }
            }
            SpecProposition::ResourceContains { parent, child } => {
                SpecProposition::ResourceContains {
                    parent: self.rewrite_spec_resource(parent)?,
                    child: self.rewrite_spec_resource(child)?,
                }
            }
            SpecProposition::MemoryLoadable {
                memory,
                base,
                start,
                end,
                element_width,
            } => SpecProposition::MemoryLoadable {
                memory: memory.clone(),
                base: self.rewrite_spec_expression(base)?,
                start: self.rewrite_spec_expression(start)?,
                end: self.rewrite_spec_expression(end)?,
                element_width: *element_width,
            },
            SpecProposition::Defined(expression) => {
                SpecProposition::Defined(self.rewrite_spec_expression(expression)?)
            }
        };
        self.spec_status()?;
        Ok(result)
    }

    fn rewrite_spec_expression(
        &mut self,
        expression: &SpecExpression,
    ) -> Result<SpecExpression, SpecRewriteError> {
        self.spec_visit()?;
        let result = match expression {
            SpecExpression::Value(value) => SpecExpression::Value(self.value(value)),
            SpecExpression::IntegerToMachine { value, destination } => {
                SpecExpression::IntegerToMachine {
                    value: Box::new(self.rewrite_spec_integer(value)?),
                    destination: *destination,
                }
            }
            SpecExpression::ResourceField { projection, c_type } => SpecExpression::ResourceField {
                projection: projection.clone(),
                c_type: *c_type,
            },
            SpecExpression::AlgebraicMatch { scrutinee, arms } => SpecExpression::AlgebraicMatch {
                scrutinee: Box::new(self.rewrite_spec_algebraic(scrutinee)?),
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(SpecAlgebraicMatchArm {
                            variant: arm.variant.clone(),
                            bindings: arm.bindings.clone(),
                            binding_types: arm.binding_types.clone(),
                            body: self.rewrite_spec_expression(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, SpecRewriteError>>()?,
            },
            SpecExpression::CExpression(value) => {
                SpecExpression::CExpression(self.rewrite_c_expression(value)?)
            }
            SpecExpression::CountedResourceCount { name, arguments } => {
                SpecExpression::CountedResourceCount {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| {
                            argument
                                .as_ref()
                                .map(|value| self.rewrite_spec_expression(value))
                                .transpose()
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                }
            }
            SpecExpression::Add(left, right) => SpecExpression::Add(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::Subtract(left, right) => SpecExpression::Subtract(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::Multiply(left, right) => SpecExpression::Multiply(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::Divide(left, right) => SpecExpression::Divide(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::Remainder(left, right) => SpecExpression::Remainder(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::ShiftLeft(left, right) => SpecExpression::ShiftLeft(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::ShiftRight(left, right) => SpecExpression::ShiftRight(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::BitwiseAnd(left, right) => SpecExpression::BitwiseAnd(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::BitwiseOr(left, right) => SpecExpression::BitwiseOr(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::BitwiseXor(left, right) => SpecExpression::BitwiseXor(
                Box::new(self.rewrite_spec_expression(left)?),
                Box::new(self.rewrite_spec_expression(right)?),
            ),
            SpecExpression::BitwiseNot(value) => {
                SpecExpression::BitwiseNot(Box::new(self.rewrite_spec_expression(value)?))
            }
            SpecExpression::Cast(value, target_type) => {
                SpecExpression::Cast(Box::new(self.rewrite_spec_expression(value)?), *target_type)
            }
            SpecExpression::If {
                condition,
                then_branch,
                else_branch,
            } => SpecExpression::If {
                condition: Box::new(self.rewrite_spec_proposition(condition)?),
                then_branch: Box::new(self.rewrite_spec_expression(then_branch)?),
                else_branch: Box::new(self.rewrite_spec_expression(else_branch)?),
            },
            SpecExpression::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => SpecExpression::RangeFold {
                start: Box::new(self.rewrite_spec_expression(start)?),
                end: Box::new(self.rewrite_spec_expression(end)?),
                initial: Box::new(self.rewrite_spec_expression(initial)?),
                accumulator: accumulator.clone(),
                item: item.clone(),
                body: Box::new(self.rewrite_spec_expression(body)?),
            },
            SpecExpression::Let { name, value, body } => SpecExpression::Let {
                name: name.clone(),
                value: Box::new(self.rewrite_spec_expression(value)?),
                body: Box::new(self.rewrite_spec_expression(body)?),
            },
            SpecExpression::PureFunctionApplication {
                name,
                arguments,
                result_type,
            } => SpecExpression::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.rewrite_spec_argument(argument))
                    .collect::<Result<Vec<_>, _>>()?,
                result_type: *result_type,
            },
            SpecExpression::LoopEntrySnapshot(value) => {
                SpecExpression::LoopEntrySnapshot(Box::new(self.rewrite_spec_expression(value)?))
            }
            SpecExpression::PointerOffset {
                pointer,
                elements,
                byte_width,
            } => SpecExpression::PointerOffset {
                pointer: Box::new(self.rewrite_spec_expression(pointer)?),
                elements: Box::new(self.rewrite_spec_expression(elements)?),
                byte_width: *byte_width,
            },
            SpecExpression::MemoryLoad {
                memory,
                pointer,
                value_type,
            } => SpecExpression::MemoryLoad {
                memory: memory.clone(),
                pointer: Box::new(self.rewrite_spec_expression(pointer)?),
                value_type: *value_type,
            },
        };
        self.spec_status()?;
        Ok(result)
    }

    fn rewrite_spec_integer(
        &mut self,
        expression: &SpecIntegerExpression,
    ) -> Result<SpecIntegerExpression, SpecRewriteError> {
        self.spec_visit()?;
        let result = match expression {
            SpecIntegerExpression::ResourceField(projection) => {
                SpecIntegerExpression::ResourceField(projection.clone())
            }
            SpecIntegerExpression::Term(term) => SpecIntegerExpression::Term(self.integer(term)),
            SpecIntegerExpression::PureFunctionApplication { name, arguments } => {
                SpecIntegerExpression::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| self.rewrite_spec_argument(argument))
                        .collect::<Result<Vec<_>, _>>()?,
                }
            }
            SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
                SpecIntegerExpression::AlgebraicMatch {
                    scrutinee: Box::new(self.rewrite_spec_algebraic(scrutinee)?),
                    arms: arms
                        .iter()
                        .map(|arm| self.rewrite_spec_integer_match_arm(arm))
                        .collect::<Result<Vec<_>, _>>()?,
                }
            }
            SpecIntegerExpression::FromMachine(value) => {
                SpecIntegerExpression::FromMachine(Box::new(self.rewrite_spec_expression(value)?))
            }
            SpecIntegerExpression::Negate(value) => {
                SpecIntegerExpression::Negate(Box::new(self.rewrite_spec_integer(value)?))
            }
            SpecIntegerExpression::Add(left, right) => SpecIntegerExpression::Add(
                Box::new(self.rewrite_spec_integer(left)?),
                Box::new(self.rewrite_spec_integer(right)?),
            ),
            SpecIntegerExpression::Subtract(left, right) => SpecIntegerExpression::Subtract(
                Box::new(self.rewrite_spec_integer(left)?),
                Box::new(self.rewrite_spec_integer(right)?),
            ),
            SpecIntegerExpression::Multiply(left, right) => SpecIntegerExpression::Multiply(
                Box::new(self.rewrite_spec_integer(left)?),
                Box::new(self.rewrite_spec_integer(right)?),
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
                            start: Box::new(self.rewrite_spec_expression(start)?),
                            end: Box::new(self.rewrite_spec_expression(end)?),
                        }
                    }
                    SpecIntegerRangeFoldIndex::Integer { start, end } => {
                        SpecIntegerRangeFoldIndex::Integer {
                            start: Box::new(self.rewrite_spec_integer(start)?),
                            end: Box::new(self.rewrite_spec_integer(end)?),
                        }
                    }
                };
                let initial = self.rewrite_spec_integer(initial)?;
                let item_carrier = match index {
                    SpecIntegerRangeFoldIndex::Int32 { .. } => BindingCarrier::C,
                    SpecIntegerRangeFoldIndex::Integer { .. } => BindingCarrier::Integer,
                };
                let (accumulator, (item, body)) =
                    self.with_spec_scope(BindingCarrier::Integer, *accumulator, |rewrite| {
                        rewrite.with_spec_scope(item_carrier, *item, |rewrite| {
                            rewrite.rewrite_spec_integer(body)
                        })
                    })?;
                SpecIntegerExpression::RangeFold {
                    index,
                    initial: Box::new(initial),
                    accumulator,
                    item,
                    body: Box::new(body),
                }
            }
        };
        self.spec_status()?;
        Ok(result)
    }

    fn rewrite_spec_integer_match_arm(
        &mut self,
        arm: &SpecIntegerMatchArm,
    ) -> Result<SpecIntegerMatchArm, SpecRewriteError> {
        if arm.bindings.len() != arm.binding_types.len()
            || arm.bindings.len() != arm.binding_variables.len()
        {
            return Err(SpecRewriteError::UnsupportedCarrier);
        }
        let (mut binding_variables, body) = self.rewrite_spec_integer_match_bindings(arm, 0)?;
        binding_variables.reverse();
        Ok(SpecIntegerMatchArm {
            variant: arm.variant.clone(),
            bindings: arm.bindings.clone(),
            binding_types: arm.binding_types.clone(),
            binding_variables,
            body: Box::new(body),
        })
    }

    fn rewrite_spec_integer_match_bindings(
        &mut self,
        arm: &SpecIntegerMatchArm,
        index: usize,
    ) -> Result<(Vec<Option<Variable>>, SpecIntegerExpression), SpecRewriteError> {
        if index == arm.bindings.len() {
            return Ok((Vec::new(), self.rewrite_spec_integer(&arm.body)?));
        }
        let binding_type = &arm.binding_types[index];
        let binding_variable = arm.binding_variables[index];
        match (binding_type, binding_variable) {
            (AlgebraicValueType::Integer, Some(variable)) => {
                let (variable, (mut variables, body)) =
                    self.with_spec_scope(BindingCarrier::Integer, variable, |rewrite| {
                        rewrite.rewrite_spec_integer_match_bindings(arm, index + 1)
                    })?;
                variables.push(Some(variable));
                Ok((variables, body))
            }
            (AlgebraicValueType::Integer, None) => Err(SpecRewriteError::UnsupportedCarrier),
            (_, Some(_)) => Err(SpecRewriteError::UnsupportedCarrier),
            (_, None) => {
                let (mut variables, body) =
                    self.rewrite_spec_integer_match_bindings(arm, index + 1)?;
                variables.push(None);
                Ok((variables, body))
            }
        }
    }

    fn rewrite_spec_algebraic(
        &mut self,
        expression: &SpecAlgebraicExpression,
    ) -> Result<SpecAlgebraicExpression, SpecRewriteError> {
        self.spec_visit()?;
        let node = match &expression.node {
            SpecAlgebraicExpressionNode::Variable(variable) => {
                if let Some(mapped) = self.scope.algebraic.get(variable) {
                    SpecAlgebraicExpressionNode::Variable(*mapped)
                } else if self
                    .typed_variables
                    .as_ref()
                    .is_some_and(|replacements| replacements.algebraic.contains_key(variable))
                {
                    // The resource path has no algebraic replacements.  A
                    // future caller must add a checked conversion to the Spec
                    // algebraic carrier rather than silently retaining this
                    // variable.
                    return Err(SpecRewriteError::UnsupportedCarrier);
                } else {
                    SpecAlgebraicExpressionNode::Variable(*variable)
                }
            }
            SpecAlgebraicExpressionNode::Binding(name) => {
                SpecAlgebraicExpressionNode::Binding(name.clone())
            }
            SpecAlgebraicExpressionNode::ResourceField(projection) => {
                SpecAlgebraicExpressionNode::ResourceField(projection.clone())
            }
            SpecAlgebraicExpressionNode::Constructor { variant, fields } => {
                SpecAlgebraicExpressionNode::Constructor {
                    variant: variant.clone(),
                    fields: fields
                        .iter()
                        .map(|field| self.rewrite_spec_value(field))
                        .collect::<Result<Vec<_>, _>>()?,
                }
            }
            SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
                SpecAlgebraicExpressionNode::Match {
                    scrutinee: Box::new(self.rewrite_spec_algebraic(scrutinee)?),
                    arms: arms
                        .iter()
                        .map(|arm| {
                            Ok(SpecAlgebraicResultMatchArm {
                                variant: arm.variant.clone(),
                                bindings: arm.bindings.clone(),
                                binding_types: arm.binding_types.clone(),
                                body: Box::new(self.rewrite_spec_algebraic(&arm.body)?),
                            })
                        })
                        .collect::<Result<Vec<_>, SpecRewriteError>>()?,
                }
            }
            SpecAlgebraicExpressionNode::PureFunctionApplication { name, arguments } => {
                SpecAlgebraicExpressionNode::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| self.rewrite_spec_argument(argument))
                        .collect::<Result<Vec<_>, _>>()?,
                }
            }
        };
        self.spec_status()?;
        Ok(SpecAlgebraicExpression {
            algebraic_type: expression.algebraic_type.clone(),
            node,
        })
    }

    fn rewrite_spec_value(
        &mut self,
        value: &SpecAlgebraicValue,
    ) -> Result<SpecAlgebraicValue, SpecRewriteError> {
        Ok(match value {
            SpecAlgebraicValue::C(value) => {
                SpecAlgebraicValue::C(self.rewrite_spec_expression(value)?)
            }
            SpecAlgebraicValue::Integer(value) => {
                SpecAlgebraicValue::Integer(self.rewrite_spec_integer(value)?)
            }
            SpecAlgebraicValue::Algebraic(value) => {
                SpecAlgebraicValue::Algebraic(self.rewrite_spec_algebraic(value)?)
            }
        })
    }

    fn rewrite_spec_argument(
        &mut self,
        argument: &SpecPureFunctionArgument,
    ) -> Result<SpecPureFunctionArgument, SpecRewriteError> {
        Ok(match argument {
            SpecPureFunctionArgument::Value(value) => {
                SpecPureFunctionArgument::Value(self.rewrite_spec_expression(value)?)
            }
            SpecPureFunctionArgument::Integer(value) => {
                SpecPureFunctionArgument::Integer(self.rewrite_spec_integer(value)?)
            }
            SpecPureFunctionArgument::Algebraic(value) => {
                SpecPureFunctionArgument::Algebraic(self.rewrite_spec_algebraic(value)?)
            }
            SpecPureFunctionArgument::ArrayRef {
                memory,
                pointer,
                element_type,
            } => SpecPureFunctionArgument::ArrayRef {
                memory: memory.clone(),
                pointer: self.rewrite_spec_expression(pointer)?,
                element_type: *element_type,
            },
        })
    }

    fn rewrite_spec_predicate_argument(
        &mut self,
        argument: &SpecPredicateArgument,
    ) -> Result<SpecPredicateArgument, SpecRewriteError> {
        Ok(match argument {
            SpecPredicateArgument::Value(value) => {
                SpecPredicateArgument::Value(self.rewrite_spec_expression(value)?)
            }
            SpecPredicateArgument::ArrayRef { memory, pointer } => {
                SpecPredicateArgument::ArrayRef {
                    memory: memory.clone(),
                    pointer: self.rewrite_spec_expression(pointer)?,
                }
            }
        })
    }

    fn rewrite_spec_sequence(
        &mut self,
        sequence: &SpecSequenceExpression,
    ) -> Result<SpecSequenceExpression, SpecRewriteError> {
        Ok(match sequence {
            SpecSequenceExpression::Literal(values) => SpecSequenceExpression::Literal(
                values
                    .iter()
                    .map(|value| self.rewrite_spec_expression(value))
                    .collect::<Result<Vec<_>, _>>()?,
            ),
            SpecSequenceExpression::Concat(left, right) => SpecSequenceExpression::Concat(
                Box::new(self.rewrite_spec_sequence(left)?),
                Box::new(self.rewrite_spec_sequence(right)?),
            ),
        })
    }

    fn rewrite_spec_resource(
        &mut self,
        resource: &SpecResource,
    ) -> Result<SpecResource, SpecRewriteError> {
        Ok(match resource {
            SpecResource::Memory {
                base,
                start,
                end,
                element_width,
            } => SpecResource::Memory {
                base: self.rewrite_spec_expression(base)?,
                start: self.rewrite_spec_expression(start)?,
                end: self.rewrite_spec_expression(end)?,
                element_width: *element_width,
            },
            SpecResource::Composite { name, arguments } => SpecResource::Composite {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.rewrite_spec_expression(argument))
                    .collect::<Result<Vec<_>, _>>()?,
            },
            SpecResource::Token { name, arguments } => SpecResource::Token {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| self.rewrite_spec_expression(argument))
                    .collect::<Result<Vec<_>, _>>()?,
            },
        })
    }

    fn rewrite_c_expression(
        &mut self,
        expression: &CExpression,
    ) -> Result<CExpression, SpecRewriteError> {
        self.spec_visit()?;
        let result = match expression {
            CExpression::Value(value) => CExpression::Value(self.value(value)),
            CExpression::Variable(name) => CExpression::Variable(name.clone()),
            CExpression::FunctionAddress(name) => CExpression::FunctionAddress(name.clone()),
            CExpression::Cast {
                expression,
                target_type,
                pointee_volatile,
                pointee_constant,
            } => CExpression::Cast {
                expression: Box::new(self.rewrite_c_expression(expression)?),
                target_type: *target_type,
                pointee_volatile: *pointee_volatile,
                pointee_constant: *pointee_constant,
            },
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => CExpression::Conditional {
                condition: Box::new(self.rewrite_c_expression(condition)?),
                then_branch: Box::new(self.rewrite_c_expression(then_branch)?),
                else_branch: Box::new(self.rewrite_c_expression(else_branch)?),
            },
            CExpression::FloatNegate(value) => {
                CExpression::FloatNegate(Box::new(self.rewrite_c_expression(value)?))
            }
            CExpression::FloatClassification {
                expression,
                classification,
            } => CExpression::FloatClassification {
                expression: Box::new(self.rewrite_c_expression(expression)?),
                classification: *classification,
            },
            CExpression::AddressOf(value) => {
                CExpression::AddressOf(Box::new(self.rewrite_c_expression(value)?))
            }
            CExpression::PointerOffsetBytes { pointer, bytes } => CExpression::PointerOffsetBytes {
                pointer: Box::new(self.rewrite_c_expression(pointer)?),
                bytes: *bytes,
            },
            CExpression::LessThan(left, right) => CExpression::LessThan(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::LessEqual(left, right) => CExpression::LessEqual(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::GreaterThan(left, right) => CExpression::GreaterThan(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::GreaterEqual(left, right) => CExpression::GreaterEqual(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Equal(left, right) => CExpression::Equal(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::NotEqual(left, right) => CExpression::NotEqual(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Not(value) => {
                CExpression::Not(Box::new(self.rewrite_c_expression(value)?))
            }
            CExpression::And(left, right) => CExpression::And(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Or(left, right) => CExpression::Or(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Add(left, right) => CExpression::Add(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Subtract(left, right) => CExpression::Subtract(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Multiply(left, right) => CExpression::Multiply(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Divide(left, right) => CExpression::Divide(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::Remainder(left, right) => CExpression::Remainder(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::ShiftLeft(left, right) => CExpression::ShiftLeft(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::ShiftRight(left, right) => CExpression::ShiftRight(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::BitwiseAnd(left, right) => CExpression::BitwiseAnd(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::BitwiseOr(left, right) => CExpression::BitwiseOr(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::BitwiseXor(left, right) => CExpression::BitwiseXor(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
            CExpression::BitwiseNot(value) => {
                CExpression::BitwiseNot(Box::new(self.rewrite_c_expression(value)?))
            }
            CExpression::Load(value) => {
                CExpression::Load(Box::new(self.rewrite_c_expression(value)?))
            }
            CExpression::TypedLoad {
                pointer,
                value_type,
                volatile,
            } => CExpression::TypedLoad {
                pointer: Box::new(self.rewrite_c_expression(pointer)?),
                value_type: *value_type,
                volatile: *volatile,
            },
            CExpression::Index(left, right) => CExpression::Index(
                Box::new(self.rewrite_c_expression(left)?),
                Box::new(self.rewrite_c_expression(right)?),
            ),
        };
        self.spec_status()?;
        Ok(result)
    }

    fn with_spec_scope<T>(
        &mut self,
        carrier: BindingCarrier,
        variable: Variable,
        body: impl FnOnce(&mut Self) -> Result<T, SpecRewriteError>,
    ) -> Result<(Variable, T), SpecRewriteError> {
        self.ensure_replacement_carriers();
        self.spec_status()?;
        let replacement_capture = self
            .replacement_carriers
            .as_ref()
            .is_some_and(|replacement| replacement.contains(carrier, variable));
        let existing_scope = match carrier {
            BindingCarrier::C => self.scope.c.contains_key(&variable),
            BindingCarrier::Integer => self.scope.integer.contains_key(&variable),
            BindingCarrier::Algebraic => self.scope.algebraic.contains_key(&variable),
        };
        let shadows_source = self.binding_shadows_source(carrier, variable);
        if !replacement_capture && !existing_scope && !shadows_source {
            let result = body(self)?;
            return Ok((variable, result));
        }

        let mapped = if replacement_capture {
            self.fresh_variable()
                .ok_or(SpecRewriteError::WorkLimitExceeded)?
        } else {
            variable
        };
        let saved_scope_id = self.scope_id;
        let saved_shadowed = self.integer_shadowed;
        let mut changes = Vec::new();
        self.push_binding_mapping(carrier, variable, mapped, &mut changes);
        if matches!(carrier, BindingCarrier::Integer)
            && shadows_source
            && !replacement_capture
            && !self.integer_shadowed
        {
            self.integer_shadowed = true;
            self.bump_scope_id();
        }
        let result = body(self);
        self.restore_scope(&changes, saved_scope_id, saved_shadowed);
        let result = result?;
        self.spec_status()?;
        Ok((mapped, result))
    }
}

impl<'a> TermRewrite<'a> {
    /// Checked variant used by the resource matcher.  Existing callers of
    /// `for_typed_variables` intentionally retain its unbounded rewrite
    /// behavior; the Spec resource path must participate in the active
    /// tactic deadline from replacement collection onward.
    pub(crate) fn for_checked_typed_variables(
        c: &'a BTreeMap<Variable, TypedCReplacement>,
        integer: &'a BTreeMap<Variable, IntegerTerm>,
        algebraic: &'a BTreeMap<Variable, AlgebraicTerm>,
    ) -> Self {
        let mut rewrite = Self::for_typed_variables(c, integer, algebraic);
        rewrite.enforce_integer_work_limit = true;
        rewrite.ensure_replacement_carriers();
        rewrite
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn rewrite_with_integer_replacement(
        source: Variable,
        replacement: IntegerTerm,
        proposition: &SpecProposition,
    ) -> Result<SpecProposition, SpecRewriteError> {
        let c_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::from([(source, replacement)]);
        let algebraic_replacements = BTreeMap::new();
        let mut rewrite = TermRewrite::for_checked_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        rewrite.spec_proposition(proposition)
    }

    #[test]
    fn checked_spec_rewrite_visits_integer_to_machine_casts() {
        let source = Variable(41);
        let proposition = SpecProposition::Comparison {
            left: SpecExpression::IntegerToMachine {
                value: Box::new(SpecIntegerExpression::Term(IntegerTerm::var(source))),
                destination: MachineIntegerType::Int32,
            },
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(7))),
        };
        let rewritten =
            rewrite_with_integer_replacement(source, IntegerTerm::constant_i64(7), &proposition)
                .unwrap();
        let SpecProposition::Comparison {
            left:
                SpecExpression::IntegerToMachine {
                    value,
                    destination: MachineIntegerType::Int32,
                },
            ..
        } = rewritten
        else {
            panic!("the checked rewrite dropped the explicit Integer cast")
        };
        assert_eq!(
            *value,
            SpecIntegerExpression::Term(IntegerTerm::constant_i64(7))
        );
    }

    #[test]
    fn checked_spec_rewrite_freshens_nested_integer_binder() {
        let source = Variable(42);
        let free = Variable(43);
        let proposition = SpecProposition::ForAllInteger {
            name: "q".into(),
            variable: free,
            body: Box::new(SpecProposition::IntegerComparison {
                left: SpecIntegerExpression::Term(IntegerTerm::var(source)),
                operator: IntegerComparisonOperator::GreaterEqual,
                right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
            }),
        };
        let rewritten =
            rewrite_with_integer_replacement(source, IntegerTerm::var(free), &proposition).unwrap();
        let SpecProposition::ForAllInteger { variable, body, .. } = rewritten else {
            panic!("the checked rewrite dropped the Integer quantifier")
        };
        assert_ne!(variable, free, "the nested binder captured the replacement");
        let SpecProposition::IntegerComparison { left, .. } = *body else {
            panic!("the Integer quantifier body changed carrier")
        };
        assert_eq!(left, SpecIntegerExpression::Term(IntegerTerm::var(free)));
    }

    #[test]
    fn checked_spec_rewrite_reserves_free_source_ids_before_freshening() {
        let source = Variable(100);
        let binder = Variable(99);
        let free_source = Variable(0);
        let proposition = SpecProposition::ForAllInteger {
            name: "q".into(),
            variable: binder,
            body: Box::new(SpecProposition::IntegerComparison {
                left: SpecIntegerExpression::Term(IntegerTerm::var(source)),
                operator: IntegerComparisonOperator::Equal,
                right: SpecIntegerExpression::Term(IntegerTerm::var(free_source)),
            }),
        };

        // The replacement captures the quantified binder.  The body also
        // contains a separate free ID 0; a fresh allocator that sees only
        // the first Integer leaf would incorrectly choose ID 0 and capture
        // that source value.
        let rewritten =
            rewrite_with_integer_replacement(source, IntegerTerm::var(binder), &proposition)
                .unwrap();
        let SpecProposition::ForAllInteger { variable, body, .. } = rewritten else {
            panic!("the checked rewrite dropped the Integer quantifier")
        };
        assert_ne!(variable, free_source);
        assert_ne!(variable, binder);
        let SpecProposition::IntegerComparison { left, right, .. } = *body else {
            panic!("the checked rewrite dropped the Integer comparison")
        };
        assert_eq!(left, SpecIntegerExpression::Term(IntegerTerm::var(binder)));
        assert_eq!(
            right,
            SpecIntegerExpression::Term(IntegerTerm::var(free_source))
        );
    }

    #[test]
    fn checked_spec_rewrite_reserves_free_c_source_ids_before_freshening() {
        let source = Variable(100);
        let binder = Variable(99);
        let free_source = Variable(0);
        let proposition = SpecProposition::ForAllInt32 {
            name: "q".into(),
            variable: binder,
            body: Box::new(SpecProposition::Comparison {
                left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(source))),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(free_source))),
            }),
        };
        let c_replacements = BTreeMap::from([(
            source,
            TypedCReplacement::Bitvector(Bitvector32Term::Variable(binder)),
        )]);
        let integer_replacements = BTreeMap::new();
        let algebraic_replacements = BTreeMap::new();
        let mut rewrite = TermRewrite::for_checked_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let rewritten = rewrite.spec_proposition(&proposition).unwrap();

        let SpecProposition::ForAllInt32 { variable, body, .. } = rewritten else {
            panic!("the checked rewrite dropped the C quantifier")
        };
        assert_ne!(variable, free_source);
        assert_ne!(variable, binder);
        assert_ne!(variable, source);
        let SpecProposition::Comparison { left, right, .. } = *body else {
            panic!("the checked rewrite dropped the C comparison")
        };
        assert_eq!(
            left,
            SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(binder)))
        );
        assert_eq!(
            right,
            SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(free_source)))
        );
    }

    #[test]
    fn checked_spec_rewrite_reserves_integer_ids_hidden_in_registered_load_offsets() {
        let memory: SharedCMemory = CMemory::new().into();
        let pointer = Pointer {
            block: PointerBlock::Symbolic(Variable(101)),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::IntegerToMachine {
                    value: IntegerTerm::var(Variable(0)).into(),
                    destination: MachineIntegerType::Int32,
                }),
                byte_width: 4,
            },
        };
        // The visible C term contains only the registered load variable.  Its
        // pointer offset retains the free Integer ID 0, which must still be
        // reserved before a C binder is freshened.
        let load = crate::kernel::eval::load_variable_for_cell(&memory, &pointer);
        let source = Variable(100);
        let binder = Variable(99);
        let free_integer = Variable(0);
        let proposition = SpecProposition::ForAllInt32 {
            name: "q".into(),
            variable: binder,
            body: Box::new(SpecProposition::Comparison {
                left: SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(source))),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(load))),
            }),
        };
        let c_replacements = BTreeMap::from([(
            source,
            TypedCReplacement::Bitvector(Bitvector32Term::Variable(binder)),
        )]);
        let integer_replacements = BTreeMap::new();
        let algebraic_replacements = BTreeMap::new();
        let mut rewrite = TermRewrite::for_checked_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let rewritten = rewrite.spec_proposition(&proposition).unwrap();

        let SpecProposition::ForAllInt32 { variable, .. } = rewritten else {
            panic!("the checked rewrite dropped the registered-load quantifier")
        };
        assert_ne!(
            variable, free_integer,
            "the load's hidden Integer offset was captured by the C binder"
        );
        assert_ne!(variable, binder);
        assert_ne!(variable, source);
    }

    #[test]
    fn checked_spec_rewrite_reserves_all_facts_before_reusing_the_walker() {
        let source = Variable(100);
        let binder = Variable(99);
        let later_free_source = Variable(102);
        let first = SpecProposition::ForAllInteger {
            name: "first".into(),
            variable: binder,
            body: Box::new(SpecProposition::IntegerComparison {
                left: SpecIntegerExpression::Term(IntegerTerm::var(source)),
                operator: IntegerComparisonOperator::Equal,
                right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
            }),
        };
        let second = SpecProposition::ForAllInteger {
            name: "second".into(),
            variable: binder,
            body: Box::new(SpecProposition::IntegerComparison {
                left: SpecIntegerExpression::Term(IntegerTerm::var(source)),
                operator: IntegerComparisonOperator::Equal,
                right: SpecIntegerExpression::Term(IntegerTerm::var(later_free_source)),
            }),
        };
        let c_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::from([(source, IntegerTerm::var(binder))]);
        let algebraic_replacements = BTreeMap::new();
        let mut rewrite = TermRewrite::for_checked_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        rewrite
            .reserve_spec_proposition_sources([&first, &second])
            .unwrap();
        let _ = rewrite.spec_proposition(&first).unwrap();
        let rewritten = rewrite.spec_proposition(&second).unwrap();

        let SpecProposition::ForAllInteger { variable, body, .. } = rewritten else {
            panic!("the checked rewrite dropped the second Integer quantifier")
        };
        assert_ne!(variable, later_free_source);
        let SpecProposition::IntegerComparison { right, .. } = *body else {
            panic!("the checked rewrite dropped the second Integer comparison")
        };
        assert_eq!(
            right,
            SpecIntegerExpression::Term(IntegerTerm::var(later_free_source))
        );
    }

    #[test]
    fn checked_spec_rewrite_match_bindings_scale_with_arity() {
        let mut samples = Vec::new();
        for arity in [4usize, 8, 16, 32] {
            let arm = SpecIntegerMatchArm {
                variant: "Node".into(),
                bindings: (0..arity).map(|index| format!("v{index}")).collect(),
                binding_types: vec![AlgebraicValueType::Integer; arity],
                binding_variables: (0..arity)
                    .map(|index| Some(Variable(100 + index as u64)))
                    .collect(),
                body: Box::new(SpecIntegerExpression::Term(IntegerTerm::constant_i64(0))),
            };
            let c_replacements = BTreeMap::new();
            let integer_replacements = BTreeMap::new();
            let algebraic_replacements = BTreeMap::new();
            let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut rewrite = TermRewrite::for_checked_typed_variables(
                    &c_replacements,
                    &integer_replacements,
                    &algebraic_replacements,
                );
                rewrite.rewrite_spec_integer_match_arm(&arm)
            });
            let rewritten = rewritten.unwrap();
            assert_eq!(rewritten.binding_variables, arm.binding_variables);
            samples.push((arity, work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 2 + 64,
                "Integer match binding rewrite grew superlinearly: {samples:?}"
            );
        }
    }

    #[test]
    fn checked_spec_rewrite_separates_int32_fold_item_from_integer_replacement() {
        let source = Variable(44);
        let free_machine = Variable(45);
        let fold_item = free_machine;
        let replacement = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(free_machine),
        ));
        let proposition = SpecProposition::IntegerComparison {
            left: SpecIntegerExpression::RangeFold {
                index: SpecIntegerRangeFoldIndex::Int32 {
                    start: Box::new(SpecExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant(0),
                    ))),
                    end: Box::new(SpecExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant(1),
                    ))),
                },
                initial: Box::new(SpecIntegerExpression::Term(IntegerTerm::var(source))),
                accumulator: Variable(46),
                item: fold_item,
                body: Box::new(SpecIntegerExpression::Add(
                    Box::new(SpecIntegerExpression::Term(IntegerTerm::var(source))),
                    Box::new(SpecIntegerExpression::FromMachine(Box::new(
                        SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(fold_item))),
                    ))),
                )),
            },
            operator: IntegerComparisonOperator::Equal,
            right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
        };
        let rewritten =
            rewrite_with_integer_replacement(source, replacement, &proposition).unwrap();
        let SpecProposition::IntegerComparison { left, .. } = rewritten else {
            panic!("the checked rewrite dropped the fold")
        };
        let SpecIntegerExpression::RangeFold {
            item,
            initial,
            body,
            ..
        } = left
        else {
            panic!("the checked rewrite dropped the Int32 fold carrier")
        };
        assert_ne!(item, fold_item, "the Int32 item captured a machine payload");
        assert_eq!(
            *initial,
            SpecIntegerExpression::Term(IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(free_machine),
            ),))
        );
        let SpecIntegerExpression::Add(left, right) = *body else {
            panic!("the checked rewrite dropped the fold body")
        };
        assert_eq!(
            *left,
            SpecIntegerExpression::Term(IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(free_machine),
            ),))
        );
        let SpecIntegerExpression::FromMachine(value) = *right else {
            panic!("the Int32 item lost its machine carrier")
        };
        let SpecExpression::Value(CValue::Int32(Bitvector32Term::Variable(rewritten_item))) =
            *value
        else {
            panic!("the Int32 item was not rewritten as a C value")
        };
        assert_eq!(rewritten_item, item);
    }

    #[test]
    fn checked_spec_rewrite_scales_with_nested_spec_nodes() {
        let source = Variable(47);
        let mut samples = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let mut proposition = SpecProposition::IntegerComparison {
                left: SpecIntegerExpression::Term(IntegerTerm::var(source)),
                operator: IntegerComparisonOperator::Equal,
                right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(7)),
            };
            for _ in 0..depth {
                proposition = SpecProposition::Not(Box::new(proposition));
            }
            let c_replacements = BTreeMap::new();
            let integer_replacements = BTreeMap::from([(source, IntegerTerm::constant_i64(7))]);
            let algebraic_replacements = BTreeMap::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut rewrite = TermRewrite::for_checked_typed_variables(
                    &c_replacements,
                    &integer_replacements,
                    &algebraic_replacements,
                );
                rewrite.spec_proposition(&proposition)
            });
            assert!(result.is_ok());
            samples.push((depth, work));
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1 * 2 + 64,
                "checked Spec rewrite grew superlinearly: {samples:?}"
            );
        }
    }

    #[test]
    fn checked_spec_rewrite_refuses_an_exhausted_work_budget() {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 0,
            smart: 0,
            control: 0,
        };
        let result = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                let tactic = crate::instrumentation::TacticEvent {
                    claim: "checked Spec rewrite".into(),
                    tactic_index: 0,
                    tactic_name: "checked_spec_rewrite".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let source = Variable(48);
                let proposition = SpecProposition::IntegerComparison {
                    left: SpecIntegerExpression::Term(IntegerTerm::var(source)),
                    operator: IntegerComparisonOperator::Equal,
                    right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(7)),
                };
                let result = rewrite_with_integer_replacement(
                    source,
                    IntegerTerm::constant_i64(7),
                    &proposition,
                );
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                );
                result
            })
            .0
        });
        assert_eq!(result, Err(SpecRewriteError::WorkLimitExceeded));
    }
}
