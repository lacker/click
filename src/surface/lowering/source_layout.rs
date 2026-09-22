use super::*;
use crate::surface::syntax::flatten_direct_c0_statements;

pub(in crate::surface) fn count_loops(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Seq(first, second) => count_loops(first) + count_loops(second),
        syntax::C0Statement::If {
            then_branch,
            else_branch,
            ..
        } => count_loops(then_branch) + count_loops(else_branch),
        syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
            1 + count_loops(body)
        }
        syntax::C0Statement::For {
            initializer,
            step,
            body,
            ..
        } => count_loops(initializer) + 1 + count_loops(body) + count_loops(step),
        syntax::C0Statement::Switch { cases, .. } => {
            cases.iter().map(|case| count_loops(case.body())).sum()
        }
        _ => 0,
    }
}

pub(in crate::surface) fn count_loop_regions(function: &syntax::C0Function) -> usize {
    count_loops(function.body()) + usize::from(function.natural_control_loop().is_some())
}

#[derive(Clone, Default)]
pub(in crate::surface) struct SourceExecutionLayout {
    data: std::sync::Arc<SourceExecutionLayoutData>,
}

#[derive(Default)]
struct SourceExecutionLayoutData {
    statements: BTreeMap<usize, SourceStatementRegion>,
    automatic_exits: BTreeMap<usize, Vec<String>>,
    automatic_abrupt_exits: BTreeMap<usize, Vec<String>>,
    automatic_break_heads: BTreeMap<usize, usize>,
    loop_bodies: BTreeMap<usize, usize>,
    natural_loop_targets: BTreeMap<usize, crate::kernel::CControlTargetId>,
    natural_exit_targets: BTreeMap<usize, crate::kernel::CControlTargetId>,
    natural_exit_statement_indices: BTreeMap<usize, usize>,
    /// The C `if` statement indices whose regions complete when the keyed
    /// statement completes normally: the chain of enclosing branches this
    /// statement ends. Statically derived, so branch-region exits need no
    /// runtime continuation bookkeeping.
    exited_branch_regions: BTreeMap<usize, Vec<usize>>,
}

#[derive(Clone, Copy)]
pub(in crate::surface) struct SourceStatementRegion {
    pub(in crate::surface) continuation_node: usize,
    pub(in crate::surface) kind: SourceStatementKind,
}

#[derive(Clone, Copy)]
pub(in crate::surface) enum SourceStatementKind {
    Plain,
    If {
        then_statement_index: usize,
        else_statement_index: usize,
    },
    Loop {
        loop_index: usize,
    },
    /// A `try` whose body and handler the stepper descends into, so an
    /// implicit cleanup call inside either one is its own steppable
    /// statement. Only the typed C++ frontend produces `TryCatchInt32`,
    /// so C layouts never contain this kind. `after_try` is the index of
    /// the first statement after the `try`, used to resume normal control
    /// flow when the body (or handler) completes.
    Try {
        try_statement_index: usize,
        handler_statement_index: usize,
        after_try_statement_index: usize,
    },
}

impl SourceExecutionLayout {
    pub(in crate::surface) fn for_function(
        function: &syntax::C0Function,
    ) -> Result<Self, ClickError> {
        let Some(function) = function.prelowered_kernel_function() else {
            return Ok(Self::new_for_function(function));
        };
        let mut layout = SourceExecutionLayoutData::default();
        let mut next_statement_index = 0;

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

        fn visit(
            statement: &CStatement,
            next_statement_index: &mut usize,
            layout: &mut SourceExecutionLayoutData,
        ) -> Result<usize, ClickError> {
            match statement {
                CStatement::Seq(first, second) => {
                    visit(first, next_statement_index, layout)?;
                    visit(second, next_statement_index, layout)
                }
                CStatement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let then_statement_index = *next_statement_index;
                    let then_last = visit(then_branch, next_statement_index, layout)?;
                    let else_statement_index = *next_statement_index;
                    let else_last = visit(else_branch, next_statement_index, layout)?;
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
                    Ok(statement_index)
                }
                CStatement::While { .. } | CStatement::Switch { .. } => Err(ClickError::new(
                    "typed-frontend source layout does not yet support loop or switch statements",
                )),
                CStatement::TryCatchInt32 {
                    try_body, handler, ..
                } => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let try_statement_index = *next_statement_index;
                    let try_last = visit(try_body, next_statement_index, layout)?;
                    let handler_statement_index = *next_statement_index;
                    let handler_last = visit(handler, next_statement_index, layout)?;
                    let continuation_node = *next_statement_index;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node,
                            kind: SourceStatementKind::Try {
                                try_statement_index,
                                handler_statement_index,
                                after_try_statement_index: continuation_node,
                            },
                        },
                    );
                    // Normal completion of the try body continues after the
                    // try. The handler's terminal outcomes (rethrow or return)
                    // make its continuation unreachable; keep it linked for
                    // uniformity.
                    if let Some(region) = layout.statements.get_mut(&try_last) {
                        region.continuation_node = continuation_node;
                    }
                    if let Some(region) = layout.statements.get_mut(&handler_last) {
                        region.continuation_node = continuation_node;
                    }
                    Ok(try_last)
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
                    Ok(statement_index)
                }
            }
        }
        visit(function.body(), &mut next_statement_index, &mut layout)?;
        Ok(Self {
            data: std::sync::Arc::new(layout),
        })
    }

    pub(in crate::surface) fn new(statement: &syntax::C0Statement) -> Self {
        Self::new_with_natural_loop(statement, None, None, None)
    }

    pub(in crate::surface) fn new_for_function(function: &syntax::C0Function) -> Self {
        match function.natural_control_loop() {
            Some((target, exit_target, _)) => {
                let exit_label = exit_target.and_then(|exit_target| {
                    function
                        .control_targets()
                        .iter()
                        .find(|(_, (target, _))| *target == exit_target)
                        .map(|(name, _)| name.clone())
                });
                Self::new_with_natural_loop(
                    function.body(),
                    Some(target),
                    exit_target,
                    exit_label.as_deref(),
                )
            }
            None => Self::new(function.body()),
        }
    }

    fn new_with_natural_loop(
        statement: &syntax::C0Statement,
        natural_loop_target: Option<crate::kernel::CControlTargetId>,
        natural_exit_target: Option<crate::kernel::CControlTargetId>,
        natural_exit_label: Option<&str>,
    ) -> Self {
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
                syntax::C0Statement::While { body, .. }
                | syntax::C0Statement::DoWhile { body, .. } => {
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
                syntax::C0Statement::For {
                    initializer,
                    body,
                    step,
                    ..
                } => {
                    visit(initializer, next_statement_index, next_loop_index, layout);
                    let statement_index = *next_statement_index;
                    let loop_index = *next_loop_index;
                    *next_statement_index += 1;
                    *next_loop_index += 1;
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    visit(body, next_statement_index, next_loop_index, layout);
                    visit(step, next_statement_index, next_loop_index, layout);
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
        if let Some(target) = natural_loop_target {
            let mut statements = Vec::new();
            flatten_direct_c0_statements(statement, &mut statements);
            let loop_index = 0;
            let statement_index = 0;
            let mut next_statement_index = 1;
            let mut next_loop_index = 1;
            data.loop_bodies.insert(loop_index, next_statement_index);
            data.natural_loop_targets.insert(loop_index, target);
            let exit_label_index = natural_exit_label.and_then(|name| {
                statements.iter().position(|statement| {
                    matches!(
                        statement,
                        syntax::C0Statement::Label { name: label, .. } if label == name
                    )
                })
            });
            if let Some(syntax::C0Statement::Label { statement, .. }) = statements.first() {
                visit(
                    statement,
                    &mut next_statement_index,
                    &mut next_loop_index,
                    &mut data,
                );
            }
            let cycle_tail = exit_label_index.unwrap_or(statements.len());
            for statement in statements.iter().skip(1).take(cycle_tail.saturating_sub(1)) {
                visit(
                    statement,
                    &mut next_statement_index,
                    &mut next_loop_index,
                    &mut data,
                );
            }
            if let (Some(exit_target), Some(exit_label_index)) =
                (natural_exit_target, exit_label_index)
            {
                data.natural_exit_targets.insert(loop_index, exit_target);
                data.natural_exit_statement_indices
                    .insert(loop_index, next_statement_index);
                let syntax::C0Statement::Label { statement, .. } = statements[exit_label_index]
                else {
                    unreachable!("natural exit target points to a label");
                };
                visit(
                    statement,
                    &mut next_statement_index,
                    &mut next_loop_index,
                    &mut data,
                );
            }
            data.statements.insert(
                statement_index,
                SourceStatementRegion {
                    continuation_node: next_statement_index,
                    kind: SourceStatementKind::Loop { loop_index },
                },
            );
        } else {
            visit(statement, &mut 0, &mut 0, &mut data);
        }
        collect_automatic_exits(statement, &mut data);
        Self {
            data: std::sync::Arc::new(data),
        }
    }

    /// The C `if` regions that complete when this statement completes
    /// normally, innermost first.
    pub(in crate::surface) fn exited_branch_regions(&self, index: usize) -> &[usize] {
        self.data
            .exited_branch_regions
            .get(&index)
            .map_or(&[], Vec::as_slice)
    }

    pub(in crate::surface) fn automatic_exits(&self, index: usize, abrupt: bool) -> &[String] {
        let exits = if abrupt {
            &self.data.automatic_abrupt_exits
        } else {
            &self.data.automatic_exits
        };
        exits.get(&index).map_or(&[], Vec::as_slice)
    }

    pub(in crate::surface) fn statement(&self, index: usize) -> Option<SourceStatementRegion> {
        self.data.statements.get(&index).copied()
    }

    pub(in crate::surface) fn statement_count(&self) -> usize {
        self.data.statements.len()
    }

    pub(in crate::surface) fn loop_body_entry(&self, loop_index: usize) -> Option<usize> {
        self.data.loop_bodies.get(&loop_index).copied()
    }

    pub(in crate::surface) fn natural_loop_target(
        &self,
        loop_index: usize,
    ) -> Option<crate::kernel::CControlTargetId> {
        self.data.natural_loop_targets.get(&loop_index).copied()
    }

    pub(in crate::surface) fn natural_exit_target(
        &self,
        loop_index: usize,
    ) -> Option<crate::kernel::CControlTargetId> {
        self.data.natural_exit_targets.get(&loop_index).copied()
    }

    pub(in crate::surface) fn natural_exit_statement_index(
        &self,
        loop_index: usize,
    ) -> Option<usize> {
        self.data
            .natural_exit_statement_indices
            .get(&loop_index)
            .copied()
    }
}

pub(in crate::surface) fn contract_segment_referenced_names(
    segment: &ContractSegment,
) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    collect_c_expression_referenced_names(&segment.base, &mut names);
    collect_c_expression_referenced_names(&segment.start, &mut names);
    collect_c_expression_referenced_names(&segment.end, &mut names);
    names
}

pub(in crate::surface) fn collect_resource_subject_referenced_names(
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

pub(in crate::surface) fn collect_c_expression_referenced_names(
    expression: &CExpression,
    names: &mut BTreeSet<String>,
) {
    match expression {
        CExpression::Value(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Variable(name) => {
            names.insert(name.clone());
        }
        CExpression::Cast { expression, .. } | CExpression::FloatNegate(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_c_expression_referenced_names(condition, names);
            collect_c_expression_referenced_names(then_branch, names);
            collect_c_expression_referenced_names(else_branch, names);
        }
        CExpression::FloatClassification { expression, .. } => {
            collect_c_expression_referenced_names(expression, names);
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

/// Index lexical lifetime boundaries once. Normal exits are attached to every
/// terminal source node of a scope (including a whole branch executed at once).
/// Abrupt exits visit only the scopes they leave; ordinary statements do not
/// copy their enclosing declarations or scan the function.
fn collect_automatic_exits(source: &syntax::C0Statement, layout: &mut SourceExecutionLayoutData) {
    use syntax::C0Statement as S;
    fn declarations(s: &S, names: &mut Vec<String>) {
        match s {
            S::Declare { name, .. } | S::DeclareStructValue { name, .. } => {
                names.push(name.clone())
            }
            S::Seq(a, b) => {
                declarations(a, names);
                declarations(b, names);
            }
            S::Label { statement, .. } => declarations(statement, names),
            _ => {}
        }
    }
    fn scope(
        s: &S,
        index: &mut usize,
        scopes: &mut Vec<(Vec<String>, Option<usize>)>,
        loop_head: Option<usize>,
        layout: &mut SourceExecutionLayoutData,
    ) -> Vec<usize> {
        let mut names = Vec::new();
        declarations(s, &mut names);
        scopes.push((names, loop_head));
        let tails = visit(s, index, scopes, layout);
        let (names, _) = scopes.pop().unwrap();
        for tail in &tails {
            layout
                .automatic_exits
                .entry(*tail)
                .or_default()
                .extend(names.iter().cloned());
        }
        tails
    }
    fn visit(
        s: &S,
        index: &mut usize,
        scopes: &mut Vec<(Vec<String>, Option<usize>)>,
        layout: &mut SourceExecutionLayoutData,
    ) -> Vec<usize> {
        if let S::Seq(a, b) = s {
            visit(a, index, scopes, layout);
            return visit(b, index, scopes, layout);
        }
        if let S::For {
            initializer,
            body,
            step,
            ..
        } = s
        {
            visit(initializer, index, scopes, layout);
            let head = *index;
            *index += 1;
            let mut names = Vec::new();
            declarations(initializer, &mut names);
            // The initializer belongs to the for statement, not its body.
            scopes.push((names.clone(), None));
            scope(body, index, scopes, Some(head), layout);
            visit(step, index, scopes, layout);
            scopes.pop();
            layout
                .automatic_exits
                .entry(head)
                .or_default()
                .extend(names);
            return vec![head];
        }
        let head = *index;
        *index += 1;
        match s {
            S::If {
                then_branch,
                else_branch,
                ..
            } => {
                let mut tails = vec![head];
                tails.extend(scope(then_branch, index, scopes, None, layout));
                tails.extend(scope(else_branch, index, scopes, None, layout));
                tails
            }
            S::While { body, .. } | S::DoWhile { body, .. } => {
                scope(body, index, scopes, Some(head), layout);
                vec![head]
            }
            S::Break | S::Continue | S::Return(_) | S::Goto { .. } => {
                let mut names = Vec::new();
                for (declared, loop_head) in scopes.iter().rev() {
                    names.extend(declared.iter().cloned());
                    if let Some(loop_head) = loop_head
                        && matches!(s, S::Break | S::Continue)
                    {
                        if matches!(s, S::Break) {
                            layout.automatic_break_heads.insert(head, *loop_head);
                        }
                        break;
                    }
                }
                layout.automatic_abrupt_exits.insert(head, names);
                vec![head]
            }
            // Switches are executed as a unit by the kernel, which retires
            // their own declarations. They still may end an enclosing scope.
            _ => vec![head],
        }
    }
    visit(source, &mut 0, &mut Vec::new(), layout);
    for (at, head) in std::mem::take(&mut layout.automatic_break_heads) {
        let exited = layout
            .automatic_exits
            .get(&head)
            .cloned()
            .unwrap_or_default();
        layout
            .automatic_abrupt_exits
            .entry(at)
            .or_default()
            .extend(exited);
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
                automatic_exits: BTreeMap::new(),
                automatic_abrupt_exits: BTreeMap::new(),
                automatic_break_heads: BTreeMap::new(),
                loop_bodies: BTreeMap::new(),
                natural_loop_targets: BTreeMap::new(),
                natural_exit_targets: BTreeMap::new(),
                natural_exit_statement_indices: BTreeMap::new(),
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
