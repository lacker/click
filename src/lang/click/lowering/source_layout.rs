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
    statements: BTreeMap<usize, SourceStatementRegion>,
    loop_bodies: BTreeMap<usize, usize>,
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
        fn visit(
            statement: &syntax::C0Statement,
            next_statement_index: &mut usize,
            next_loop_index: &mut usize,
            layout: &mut SourceExecutionLayout,
        ) {
            match statement {
                syntax::C0Statement::Seq(first, second) => {
                    visit(first, next_statement_index, next_loop_index, layout);
                    visit(second, next_statement_index, next_loop_index, layout);
                }
                syntax::C0Statement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let then_statement_index = *next_statement_index;
                    visit(then_branch, next_statement_index, next_loop_index, layout);
                    let else_statement_index = *next_statement_index;
                    visit(else_branch, next_statement_index, next_loop_index, layout);
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::If {
                                then_statement_index,
                                else_statement_index,
                            },
                        },
                    );
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
                }
            }
        }

        let mut layout = Self::default();
        visit(statement, &mut 0, &mut 0, &mut layout);
        layout
    }

    pub(in crate::lang::click) fn statement(&self, index: usize) -> Option<SourceStatementRegion> {
        self.statements.get(&index).copied()
    }

    pub(in crate::lang::click) fn statement_count(&self) -> usize {
        self.statements.len()
    }

    pub(in crate::lang::click) fn loop_body_entry(&self, loop_index: usize) -> Option<usize> {
        self.loop_bodies.get(&loop_index).copied()
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
