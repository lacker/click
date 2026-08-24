use super::*;

pub(in crate::lang::click) fn count_loops(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => count_loops(first) + count_loops(second),
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => count_loops(then_branch) + count_loops(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_loops(body),
        _ => 0,
    }
}

pub(in crate::lang::click) fn count_statements(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => {
            count_statements(first) + count_statements(second)
        }
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => 1 + count_statements(then_branch) + count_statements(else_branch),
        syntax::C0Statement::While { body, .. } => 1 + count_statements(body),
        _ => 1,
    }
}

#[derive(Clone, Default)]
pub(in crate::lang::click) struct SourceExecutionLayout {
    data: std::sync::Arc<SourceExecutionLayoutData>,
}

#[derive(Default)]
struct SourceExecutionLayoutData {
    statements: BTreeMap<usize, SourceStatementRegion>,
    loop_bodies: BTreeMap<usize, usize>,
    /// The C `if` statement indices whose regions complete when the keyed
    /// statement completes normally: the chain of enclosing branches this
    /// statement ends. Statically derived, so branch-region exits need no
    /// runtime continuation bookkeeping.
    exited_branch_regions: BTreeMap<usize, Vec<usize>>,
}

#[derive(Clone, Copy)]
pub(in crate::lang::click) struct SourceStatementRegion {
    pub(in crate::lang::click) continuation_node: usize,
    pub(in crate::lang::click) kind: SourceStatementKind,
}

#[derive(Clone, Copy)]
pub(in crate::lang::click) enum SourceStatementKind {
    Plain,
    If {
        then_statement_index: usize,
        else_statement_index: usize,
    },
    Loop {
        loop_index: usize,
    },
}

impl SourceExecutionLayout {
    pub(in crate::lang::click) fn new(statement: &syntax::C0Statement) -> Self {
        /// Visits one subtree and returns the pre-order index of its last
        /// top-level statement, so an enclosing `if` can redirect its arms'
        /// control successors past the sibling arm to its own continuation.
        fn visit(
            statement: &syntax::C0Statement,
            next_statement_index: &mut usize,
            next_loop_index: &mut usize,
            layout: &mut SourceExecutionLayoutData,
        ) -> usize {
            match statement {
                syntax::C0Statement::Seq(first, second) => {
                    visit(first, next_statement_index, next_loop_index, layout);
                    visit(second, next_statement_index, next_loop_index, layout)
                }
                syntax::C0Statement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let then_statement_index = *next_statement_index;
                    let then_last =
                        visit(then_branch, next_statement_index, next_loop_index, layout);
                    let else_statement_index = *next_statement_index;
                    let else_last =
                        visit(else_branch, next_statement_index, next_loop_index, layout);
                    let continuation_node = *next_statement_index;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node,
                            kind: SourceStatementKind::If {
                                then_statement_index,
                                else_statement_index,
                            },
                        },
                    );
                    // Completing either arm's last statement completes this
                    // `if` region and continues at this `if`'s continuation,
                    // not at the next pre-order statement (the sibling arm).
                    redirect_control_successor(
                        layout,
                        then_last,
                        statement_index,
                        continuation_node,
                    );
                    redirect_control_successor(
                        layout,
                        else_last,
                        statement_index,
                        continuation_node,
                    );
                    statement_index
                }
                syntax::C0Statement::While { body, .. } => {
                    let statement_index = *next_statement_index;
                    let loop_index = *next_loop_index;
                    *next_statement_index += 1;
                    *next_loop_index += 1;
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    visit(body, next_statement_index, next_loop_index, layout);
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Loop { loop_index },
                        },
                    );
                    statement_index
                }
                _ => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Plain,
                        },
                    );
                    statement_index
                }
            }
        }

        /// Redirects the control successor of an arm's last statement to the
        /// enclosing `if`'s continuation and records the completed branch
        /// region. When that last statement is itself an `if`, its own arms'
        /// tails complete both branch regions at once, recursively.
        fn redirect_control_successor(
            layout: &mut SourceExecutionLayoutData,
            last_statement_index: usize,
            exited_if_index: usize,
            continuation_node: usize,
        ) {
            let Some(region) = layout.statements.get_mut(&last_statement_index) else {
                return;
            };
            region.continuation_node = continuation_node;
            layout
                .exited_branch_regions
                .entry(last_statement_index)
                .or_default()
                .push(exited_if_index);
            if let SourceStatementKind::If { .. } = region.kind {
                let arm_lasts: Vec<usize> = layout
                    .exited_branch_regions
                    .iter()
                    .filter(|(_, exited)| exited.contains(&last_statement_index))
                    .map(|(index, _)| *index)
                    .collect();
                for arm_last in arm_lasts {
                    redirect_control_successor(
                        layout,
                        arm_last,
                        exited_if_index,
                        continuation_node,
                    );
                }
            }
        }

        let mut data = SourceExecutionLayoutData::default();
        visit(statement, &mut 0, &mut 0, &mut data);
        Self {
            data: std::sync::Arc::new(data),
        }
    }

    /// The C `if` regions that complete when this statement completes
    /// normally, innermost first.
    pub(in crate::lang::click) fn exited_branch_regions(&self, index: usize) -> &[usize] {
        self.data
            .exited_branch_regions
            .get(&index)
            .map_or(&[], Vec::as_slice)
    }

    pub(in crate::lang::click) fn statement(&self, index: usize) -> Option<SourceStatementRegion> {
        self.data.statements.get(&index).copied()
    }

    pub(in crate::lang::click) fn statement_count(&self) -> usize {
        self.data.statements.len()
    }

    pub(in crate::lang::click) fn loop_body_entry(&self, loop_index: usize) -> Option<usize> {
        self.data.loop_bodies.get(&loop_index).copied()
    }
}

#[cfg(test)]
mod source_execution_layout_tests {
    use super::*;

    #[test]
    fn clones_share_large_immutable_layouts() {
        let statements = (0..4096)
            .map(|index| {
                (
                    index,
                    SourceStatementRegion {
                        continuation_node: index + 1,
                        kind: SourceStatementKind::Plain,
                    },
                )
            })
            .collect();
        let layout = SourceExecutionLayout {
            data: std::sync::Arc::new(SourceExecutionLayoutData {
                statements,
                loop_bodies: BTreeMap::new(),
                exited_branch_regions: BTreeMap::new(),
            }),
        };
        let cloned = layout.clone();

        assert!(std::sync::Arc::ptr_eq(&layout.data, &cloned.data));
        assert_eq!(cloned.statement_count(), 4096);
        assert_eq!(
            cloned
                .statement(4095)
                .map(|region| region.continuation_node),
            Some(4096)
        );
    }
}

pub(in crate::lang::click) fn c0_loop_modified_locals(
    statement: &syntax::C0Statement,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_c0_loop_modified_locals(statement, &mut names);
    names
}

pub(in crate::lang::click) fn collect_c0_loop_modified_locals(
    statement: &syntax::C0Statement,
    names: &mut BTreeSet<String>,
) {
    match statement {
        syntax::C0Statement::Skip
        | syntax::C0Statement::Declare { .. }
        | syntax::C0Statement::Return(_)
        | syntax::C0Statement::Store { .. } => {}
        syntax::C0Statement::Assign { name, .. } => {
            names.insert(name.clone());
        }
        syntax::C0Statement::CallAssign { target, .. } => {
            names.insert(target.clone());
        }
        syntax::C0Statement::Call { .. } => {}
        syntax::C0Statement::HeapAllocate { target, .. } => {
            names.insert(target.clone());
        }
        syntax::C0Statement::HeapFree { .. } => {}
        syntax::C0Statement::Seq(first, second) => {
            collect_c0_loop_modified_locals(first, names);
            collect_c0_loop_modified_locals(second, names);
        }
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_c0_loop_modified_locals(then_branch, names);
            collect_c0_loop_modified_locals(else_branch, names);
        }
        syntax::C0Statement::While { body, .. } => {
            collect_c0_loop_modified_locals(body, names);
        }
    }
}

pub(in crate::lang::click) fn contract_segment_referenced_names(
    segment: &ContractSegment,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_c_expression_referenced_names(&segment.base, &mut names);
    collect_c_expression_referenced_names(&segment.start, &mut names);
    collect_c_expression_referenced_names(&segment.end, &mut names);
    names
}

pub(in crate::lang::click) fn collect_resource_subject_referenced_names(
    resource: &ResourceSubject,
    names: &mut BTreeSet<String>,
) {
    match resource {
        ResourceSubject::Memory(segment) => {
            names.extend(contract_segment_referenced_names(segment))
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, names);
            }
        }
    }
}

pub(in crate::lang::click) fn collect_c_expression_referenced_names(
    expression: &CExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        CExpression::Value(_) => {}
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::AddressOf(expression)
        | CExpression::Not(expression)
        | CExpression::Load(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_c_expression_referenced_names(pointer, names);
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_referenced_names(pointer, names);
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
            collect_c_expression_referenced_names(left, names);
            collect_c_expression_referenced_names(right, names);
        }
        CExpression::BitwiseNot(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
    }
}
