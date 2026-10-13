//! One walk over the specification syntax tree.
//!
//! [`SpecNode::for_each_child`] is the single list of which spec subtrees a
//! node contains, and [`walk_spec`] visits a tree in source order with an
//! explicit worklist. A question about a tree is then only its leaf rules:
//! the visitor says, per node, whether to descend, skip the node's children,
//! or stop with an answer.

use super::*;

#[cfg(test)]
pub(in crate::kernel) mod generated;

/// One spec subtree of any kind.
#[derive(Clone, Copy)]
pub(in crate::kernel) enum SpecNode<'a> {
    Proposition(&'a SpecProposition),
    Expression(&'a SpecExpression),
    Integer(&'a SpecIntegerExpression),
    Algebraic(&'a SpecAlgebraicExpression),
    AlgebraicValue(&'a SpecAlgebraicValue),
    Argument(&'a SpecPureFunctionArgument),
    PredicateArgument(&'a SpecPredicateArgument),
    Sequence(&'a SpecSequenceExpression),
    Resource(&'a SpecResource),
}

impl<'a> SpecNode<'a> {
    /// Calls `visit` on every direct spec child, in source order.
    ///
    /// Every variant is listed, so a new spec form does not compile until its
    /// children are. C expressions, memories, `IntegerTerm` leaves, and binder
    /// names are not spec children; a visitor that cares reads them from the
    /// node itself.
    pub(in crate::kernel) fn for_each_child(self, mut visit: impl FnMut(SpecNode<'a>)) {
        use SpecNode as N;
        match self {
            N::Proposition(proposition) => match proposition {
                SpecProposition::Comparison { left, right, .. } => {
                    visit(N::Expression(left));
                    visit(N::Expression(right));
                }
                SpecProposition::IntegerComparison { left, right, .. } => {
                    visit(N::Integer(left));
                    visit(N::Integer(right));
                }
                SpecProposition::AlgebraicComparison { left, right, .. } => {
                    visit(N::Algebraic(left));
                    visit(N::Algebraic(right));
                }
                SpecProposition::SequenceComparison { left, right, .. } => {
                    visit(N::Sequence(left));
                    visit(N::Sequence(right));
                }
                SpecProposition::SequenceMembership { element, sequence } => {
                    visit(N::Expression(element));
                    visit(N::Sequence(sequence));
                }
                SpecProposition::FloatClassification { expression, .. }
                | SpecProposition::Defined(expression) => visit(N::Expression(expression)),
                SpecProposition::ValidPlace { pointer, range, .. } => {
                    visit(N::Expression(pointer));
                    if let Some((start, end)) = range {
                        visit(N::Expression(start));
                        visit(N::Expression(end));
                    }
                }
                SpecProposition::MemoryInitialized { base, .. } => visit(N::Expression(base)),
                SpecProposition::And(left, right)
                | SpecProposition::Or(left, right)
                | SpecProposition::Implies(left, right) => {
                    visit(N::Proposition(left));
                    visit(N::Proposition(right));
                }
                SpecProposition::Not(body)
                | SpecProposition::ForAllMachineInteger { body, .. }
                | SpecProposition::ForAllInt32 { body, .. }
                | SpecProposition::ForAllInteger { body, .. }
                | SpecProposition::ForAllAlgebraic { body, .. }
                | SpecProposition::ForAllPointer { body, .. }
                | SpecProposition::ExistsMachineInteger { body, .. }
                | SpecProposition::ExistsInt32 { body, .. }
                | SpecProposition::ExistsInteger { body, .. }
                | SpecProposition::ExistsAlgebraic { body, .. }
                | SpecProposition::ExistsPointer { body, .. } => visit(N::Proposition(body)),
                SpecProposition::Predicate { arguments, .. } => {
                    arguments
                        .iter()
                        .for_each(|argument| visit(N::PredicateArgument(argument)));
                }
                SpecProposition::ResourceSeparate { left, right } => {
                    visit(N::Resource(left));
                    visit(N::Resource(right));
                }
                SpecProposition::ResourceContains { parent, child } => {
                    visit(N::Resource(parent));
                    visit(N::Resource(child));
                }
                SpecProposition::MemoryLoadable {
                    base, start, end, ..
                } => {
                    visit(N::Expression(base));
                    visit(N::Expression(start));
                    visit(N::Expression(end));
                }
            },
            N::Expression(expression) => match expression {
                SpecExpression::Value(_)
                | SpecExpression::CExpression(_)
                | SpecExpression::ResourceField { .. } => {}
                SpecExpression::IntegerToMachine { value, .. } => visit(N::Integer(value)),
                SpecExpression::AlgebraicMatch { scrutinee, arms } => {
                    visit(N::Algebraic(scrutinee));
                    arms.iter().for_each(|arm| visit(N::Expression(&arm.body)));
                }
                SpecExpression::CountedResourceCount { arguments, .. } => {
                    arguments
                        .iter()
                        .flatten()
                        .for_each(|argument| visit(N::Expression(argument)));
                }
                crate::kernel::binary_spec_expression!(left, right) => {
                    visit(N::Expression(left));
                    visit(N::Expression(right));
                }
                SpecExpression::BitwiseNot(body)
                | SpecExpression::Cast(body, _)
                | SpecExpression::LoopEntrySnapshot(body) => visit(N::Expression(body)),
                SpecExpression::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    visit(N::Proposition(condition));
                    visit(N::Expression(then_branch));
                    visit(N::Expression(else_branch));
                }
                SpecExpression::RangeFold {
                    start,
                    end,
                    initial,
                    body,
                    ..
                } => {
                    visit(N::Expression(start));
                    visit(N::Expression(end));
                    visit(N::Expression(initial));
                    visit(N::Expression(body));
                }
                SpecExpression::Let { value, body, .. } => {
                    visit(N::Expression(value));
                    visit(N::Expression(body));
                }
                SpecExpression::PureFunctionApplication { arguments, .. } => {
                    arguments
                        .iter()
                        .for_each(|argument| visit(N::Argument(argument)));
                }
                SpecExpression::PointerOffset {
                    pointer, elements, ..
                } => {
                    visit(N::Expression(pointer));
                    visit(N::Expression(elements));
                }
                SpecExpression::MemoryLoad { pointer, .. }
                | SpecExpression::AggregateFieldValue { pointer, .. } => {
                    visit(N::Expression(pointer))
                }
            },
            N::Integer(integer) => match integer {
                SpecIntegerExpression::ResourceField(_) | SpecIntegerExpression::Term(_) => {}
                SpecIntegerExpression::PureFunctionApplication { arguments, .. } => {
                    arguments
                        .iter()
                        .for_each(|argument| visit(N::Argument(argument)));
                }
                SpecIntegerExpression::AlgebraicMatch { scrutinee, arms } => {
                    visit(N::Algebraic(scrutinee));
                    arms.iter().for_each(|arm| visit(N::Integer(&arm.body)));
                }
                SpecIntegerExpression::FromMachine(value) => visit(N::Expression(value)),
                SpecIntegerExpression::Negate(value) => visit(N::Integer(value)),
                crate::kernel::binary_spec_integer_expression!(left, right) => {
                    visit(N::Integer(left));
                    visit(N::Integer(right));
                }
                SpecIntegerExpression::RangeFold {
                    index,
                    initial,
                    body,
                    ..
                } => {
                    match index {
                        SpecIntegerRangeFoldIndex::Int32 { start, end }
                        | SpecIntegerRangeFoldIndex::UInt64 { start, end } => {
                            visit(N::Expression(start));
                            visit(N::Expression(end));
                        }
                        SpecIntegerRangeFoldIndex::Integer { start, end } => {
                            visit(N::Integer(start));
                            visit(N::Integer(end));
                        }
                    }
                    visit(N::Integer(initial));
                    visit(N::Integer(body));
                }
            },
            N::Algebraic(algebraic) => match &algebraic.node {
                SpecAlgebraicExpressionNode::Variable(_)
                | SpecAlgebraicExpressionNode::Binding(_)
                | SpecAlgebraicExpressionNode::ResourceField(_) => {}
                SpecAlgebraicExpressionNode::Constructor { fields, .. } => {
                    fields
                        .iter()
                        .for_each(|field| visit(N::AlgebraicValue(field)));
                }
                SpecAlgebraicExpressionNode::Match { scrutinee, arms } => {
                    visit(N::Algebraic(scrutinee));
                    arms.iter().for_each(|arm| visit(N::Algebraic(&arm.body)));
                }
                SpecAlgebraicExpressionNode::PureFunctionApplication { arguments, .. } => {
                    arguments
                        .iter()
                        .for_each(|argument| visit(N::Argument(argument)));
                }
            },
            N::AlgebraicValue(value) => match value {
                SpecAlgebraicValue::C(expression) => visit(N::Expression(expression)),
                SpecAlgebraicValue::Integer(integer) => visit(N::Integer(integer)),
                SpecAlgebraicValue::Algebraic(algebraic) => visit(N::Algebraic(algebraic)),
            },
            N::Argument(argument) => match argument {
                SpecPureFunctionArgument::Value(expression)
                | SpecPureFunctionArgument::ArrayRef {
                    pointer: expression,
                    ..
                } => visit(N::Expression(expression)),
                SpecPureFunctionArgument::Integer(integer) => visit(N::Integer(integer)),
                SpecPureFunctionArgument::Algebraic(algebraic) => visit(N::Algebraic(algebraic)),
            },
            N::PredicateArgument(argument) => match argument {
                SpecPredicateArgument::Value(expression)
                | SpecPredicateArgument::ArrayRef {
                    pointer: expression,
                    ..
                } => visit(N::Expression(expression)),
            },
            N::Sequence(sequence) => match sequence {
                SpecSequenceExpression::Literal(elements) => {
                    elements
                        .iter()
                        .for_each(|element| visit(N::Expression(element)));
                }
                SpecSequenceExpression::Concat(left, right) => {
                    visit(N::Sequence(left));
                    visit(N::Sequence(right));
                }
            },
            N::Resource(resource) => match resource {
                SpecResource::Memory {
                    base, start, end, ..
                } => {
                    visit(N::Expression(base));
                    visit(N::Expression(start));
                    visit(N::Expression(end));
                }
                SpecResource::Composite { arguments, .. }
                | SpecResource::Token { arguments, .. } => {
                    arguments
                        .iter()
                        .for_each(|argument| visit(N::Expression(argument)));
                }
            },
        }
    }
}

impl SpecProposition {
    /// A quantifier's bound variable and body.
    pub(in crate::kernel) fn quantifier(&self) -> Option<(Variable, &SpecProposition)> {
        match self {
            SpecProposition::ForAllMachineInteger { variable, body, .. }
            | SpecProposition::ForAllInt32 { variable, body, .. }
            | SpecProposition::ForAllInteger { variable, body, .. }
            | SpecProposition::ForAllAlgebraic { variable, body, .. }
            | SpecProposition::ForAllPointer { variable, body, .. }
            | SpecProposition::ExistsMachineInteger { variable, body, .. }
            | SpecProposition::ExistsInt32 { variable, body, .. }
            | SpecProposition::ExistsInteger { variable, body, .. }
            | SpecProposition::ExistsAlgebraic { variable, body, .. }
            | SpecProposition::ExistsPointer { variable, body, .. } => Some((*variable, body)),
            _ => None,
        }
    }
}

/// What a visitor decides at one node.
pub(in crate::kernel) enum Visit<B> {
    /// Visit the node's children.
    Descend,
    /// Do not visit the node's children.
    Skip,
    /// End the walk with this answer.
    Stop(B),
}

/// Whether a walk observes the verification deadline.
#[derive(Clone, Copy)]
pub(in crate::kernel) enum WalkBudget {
    /// No deadline check; the walk is bounded by the tree.
    Unmetered,
    /// One unit of work per node; the walk ends when the deadline passes.
    Deadline,
}

/// How a walk ended.
pub(in crate::kernel) enum Walked<B> {
    /// Every node the visitor descended to was visited.
    Completed,
    /// The visitor stopped with this answer.
    Stopped(B),
    /// The deadline passed before the walk finished.
    OutOfTime,
}

/// Visits `root` and its descendants in source order (pre-order, left to
/// right), asking `visit` at each node whether to descend.
pub(in crate::kernel) fn walk_spec<'a, B>(
    root: SpecNode<'a>,
    budget: WalkBudget,
    mut visit: impl FnMut(SpecNode<'a>) -> Visit<B>,
) -> Walked<B> {
    let mut pending = Vec::with_capacity(8);
    pending.push(root);
    let mut children = Vec::new();
    while let Some(node) = pending.pop() {
        if matches!(budget, WalkBudget::Deadline)
            && crate::instrumentation::deadline_exceeded_with_work(1)
        {
            return Walked::OutOfTime;
        }
        match visit(node) {
            Visit::Descend => {
                node.for_each_child(|child| children.push(child));
                pending.extend(children.drain(..).rev());
            }
            Visit::Skip => {}
            Visit::Stop(answer) => return Walked::Stopped(answer),
        }
    }
    Walked::Completed
}

/// Whether every node of the tree passes `admits`: the walk stops at the first
/// node it refuses. For checks that read no deadline.
pub(in crate::kernel) fn spec_tree_all<'a>(
    root: SpecNode<'a>,
    admits: impl FnMut(SpecNode<'a>) -> Visit<()>,
) -> bool {
    matches!(
        walk_spec(root, WalkBudget::Unmetered, admits),
        Walked::Completed
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(value: u32) -> SpecExpression {
        SpecExpression::Value(CValue::Int32(Bitvector32Term::Constant(value)))
    }

    fn comparison(left: SpecExpression, right: SpecExpression) -> SpecProposition {
        SpecProposition::Comparison {
            left,
            operator: CComparisonOperator::Equal,
            right,
        }
    }

    /// The walk visits a node's children in source order, after the node.
    #[test]
    fn walk_is_pre_order_left_to_right() {
        let tree = SpecProposition::And(
            Box::new(comparison(int(1), int(2))),
            Box::new(comparison(
                SpecExpression::Add(Box::new(int(3)), Box::new(int(4))),
                int(5),
            )),
        );
        let mut values = Vec::new();
        let walked = walk_spec(
            SpecNode::Proposition(&tree),
            WalkBudget::Unmetered,
            |node| {
                if let SpecNode::Expression(SpecExpression::Value(CValue::Int32(bits))) = node {
                    values.push(bits.as_const().unwrap());
                }
                Visit::<()>::Descend
            },
        );
        assert!(matches!(walked, Walked::Completed));
        assert_eq!(values, [1, 2, 3, 4, 5]);
    }

    /// `Skip` hides a node's children and `Stop` ends the walk at once.
    #[test]
    fn skip_and_stop_cut_the_walk() {
        let tree = SpecProposition::And(
            Box::new(comparison(int(1), int(2))),
            Box::new(comparison(int(3), int(4))),
        );
        let mut seen = 0;
        let walked = walk_spec(
            SpecNode::Proposition(&tree),
            WalkBudget::Unmetered,
            |node| match node {
                SpecNode::Proposition(SpecProposition::Comparison {
                    left: SpecExpression::Value(CValue::Int32(bits)),
                    ..
                }) if bits.as_const() == Some(1) => Visit::Skip,
                SpecNode::Expression(_) => {
                    seen += 1;
                    if seen == 2 {
                        Visit::Stop("second")
                    } else {
                        Visit::Descend
                    }
                }
                _ => Visit::Descend,
            },
        );
        assert!(matches!(walked, Walked::Stopped("second")));
        assert_eq!(seen, 2);
    }
}
