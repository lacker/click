use super::*;
use crate::surface::syntax::flatten_direct_c0_statements;

type Site = std::sync::Arc<syntax::C0StatementSite>;

pub(in crate::surface) fn count_loops(statement: &syntax::C0Statement) -> usize {
    match statement {
        syntax::C0Statement::Scope { body } => count_loops(body),
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
    let Some(kernel) = function.prelowered_kernel_function() else {
        return count_loops(function.body())
            + usize::from(function.natural_control_loop().is_some());
    };
    let mut pending = vec![kernel.body()];
    let mut count = 0;
    while let Some(statement) = pending.pop() {
        match statement {
            CStatement::Scope { body } => pending.push(body),
            CStatement::Seq(a, b) => pending.extend([a.as_ref(), b.as_ref()]),
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => pending.extend([then_branch.as_ref(), else_branch.as_ref()]),
            CStatement::TryCatchInt32 {
                try_body, handler, ..
            } => pending.extend([try_body.as_ref(), handler.as_ref()]),
            CStatement::While { body, .. } => {
                count += 1;
                pending.push(body);
            }
            _ => {}
        }
    }
    count + usize::from(function.natural_control_loop().is_some())
}

#[derive(Clone, Default)]
pub(in crate::surface) struct SourceExecutionLayout {
    data: std::sync::Arc<SourceExecutionLayoutData>,
}

#[derive(Default)]
struct SourceExecutionLayoutData {
    statements: BTreeMap<usize, SourceStatementRegion>,
    /// Static stores to named locals, indexed once in executable preorder.
    assignments: BTreeMap<String, Vec<usize>>,
    reads: Vec<usize>,
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
    /// The inverse of `exited_branch_regions`, kept while the layout is
    /// built: for each `if`, the statements whose completion completes its
    /// region. Redirecting an arm that ends in an `if` needs exactly these,
    /// and finding them by scanning every statement's list made the build
    /// quadratic in the statements of a nested branch tree.
    arm_lasts_by_exited_region: BTreeMap<usize, Vec<usize>>,
    /// Where each C statement was written, by statement index: diagnostics
    /// only, read by a refusal to name the line it refused. Statements a
    /// frontend generated with no source statement of their own are absent.
    sites: BTreeMap<usize, std::sync::Arc<syntax::C0StatementSite>>,
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
        try_last_statement_index: usize,
        handler_last_statement_index: usize,
    },
}

// Inspect only expressions owned by this statement, never descendant bodies.
// Address-of computes an lvalue address without reading its designated cell;
// nested loads in the pointer/index expressions still count.
fn expression_reads(expression: &CExpression) -> bool {
    let mut pending = vec![(expression, true)];
    while let Some((expression, value)) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match expression {
            CExpression::Load(_) | CExpression::TypedLoad { .. } | CExpression::Index(..)
                if value =>
            {
                return true;
            }
            CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => {
                pending.push((pointer, true))
            }
            CExpression::AddressOf(place) | CExpression::CheckedObjectAddress(place) => {
                pending.push((place, false))
            }
            CExpression::Cast { expression, .. }
            | CExpression::FloatNegate(expression)
            | CExpression::FloatClassification { expression, .. }
            | CExpression::Not(expression)
            | CExpression::BitwiseNot(expression) => pending.push((expression, true)),
            CExpression::PointerOffsetBytes { pointer, .. }
            | CExpression::PointerAligned { pointer, .. }
            | CExpression::MemberAddress {
                object: pointer, ..
            } => pending.push((pointer, true)),
            CExpression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => pending.extend([
                (condition.as_ref(), true),
                (then_branch.as_ref(), true),
                (else_branch.as_ref(), true),
            ]),
            crate::kernel::binary_c_expression!(a, b) => {
                pending.extend([(a.as_ref(), true), (b.as_ref(), true)])
            }
            CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        }
    }
    false
}

fn kernel_statement_reads(statement: &CStatement) -> bool {
    match statement {
        CStatement::Assign { expression, .. }
        | CStatement::Return(expression)
        | CStatement::Throw(expression)
        | CStatement::Assert {
            condition: expression,
            ..
        }
        | CStatement::If {
            condition: expression,
            ..
        }
        | CStatement::While {
            condition: expression,
            ..
        }
        | CStatement::Switch { expression, .. }
        | CStatement::HeapAllocate {
            bytes: expression, ..
        }
        | CStatement::HeapFree {
            pointer: expression,
        } => expression_reads(expression),
        CStatement::Call { arguments, .. } | CStatement::CallAssign { arguments, .. } => {
            arguments.iter().any(expression_reads)
        }
        CStatement::Store { pointer, value } | CStatement::TypedStore { pointer, value, .. } => {
            expression_reads(pointer) || expression_reads(value)
        }
        CStatement::Update {
            target, operand, ..
        } => expression_reads(target) || expression_reads(operand),
        _ => false,
    }
}

fn syntax_statement_reads(statement: &syntax::C0Statement) -> bool {
    use syntax::C0Statement as S;
    let read =
        |expression: &syntax::C0Expression| expression_reads(&expression.to_kernel_expression());
    match statement {
        S::Assign { expression, .. }
        | S::Return(expression, _)
        | S::Assert {
            condition: expression,
            ..
        }
        | S::If {
            condition: expression,
            ..
        }
        | S::While {
            condition: expression,
            ..
        }
        | S::DoWhile {
            condition: expression,
            ..
        }
        | S::For {
            condition: expression,
            ..
        }
        | S::Switch { expression, .. }
        | S::HeapAllocate {
            bytes: expression, ..
        }
        | S::HeapFree {
            pointer: expression,
            ..
        } => read(expression),
        S::Call { arguments, .. } | S::CallAssign { arguments, .. } => arguments.iter().any(read),
        S::Store { pointer, value, .. }
        | S::SequentialStore {
            target: pointer,
            value,
            ..
        } => read(pointer) || read(value),
        S::Update {
            target, operand, ..
        } => read(target) || read(operand),
        _ => false,
    }
}

fn record_assignment(layout: &mut SourceExecutionLayoutData, local: &str, index: usize) {
    crate::instrumentation::record_deterministic_work(1);
    layout
        .assignments
        .entry(local.to_owned())
        .or_default()
        .push(index);
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
            let try_lasts = if let SourceStatementKind::Try {
                after_try_statement_index,
                try_last_statement_index,
                handler_last_statement_index,
                ..
            } = &mut region.kind
            {
                *after_try_statement_index = continuation_node;
                Some([*try_last_statement_index, *handler_last_statement_index])
            } else {
                None
            };
            layout
                .exited_branch_regions
                .entry(last_statement_index)
                .or_default()
                .push(exited_if_index);
            layout
                .arm_lasts_by_exited_region
                .entry(exited_if_index)
                .or_default()
                .push(last_statement_index);
            if let Some(lasts) = try_lasts {
                for last in lasts {
                    redirect_control_successor(layout, last, exited_if_index, continuation_node);
                }
            } else if let SourceStatementKind::If { .. } = region.kind {
                // In statement order, each statement once: what the scan of
                // every statement's list returned.
                let mut arm_lasts: Vec<usize> = layout
                    .arm_lasts_by_exited_region
                    .get(&last_statement_index)
                    .cloned()
                    .unwrap_or_default();
                arm_lasts.sort_unstable();
                arm_lasts.dedup();
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
            if kernel_statement_reads(statement) {
                layout.reads.push(*next_statement_index);
            }
            match statement {
                CStatement::Scope { body } => visit(body, next_statement_index, layout),
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
                CStatement::While { body, .. } => {
                    let statement_index = *next_statement_index;
                    *next_statement_index += 1;
                    let loop_index = layout.loop_bodies.len();
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    visit(body, next_statement_index, layout)?;
                    layout.statements.insert(
                        statement_index,
                        SourceStatementRegion {
                            continuation_node: *next_statement_index,
                            kind: SourceStatementKind::Loop { loop_index },
                        },
                    );
                    Ok(statement_index)
                }
                CStatement::Switch { .. } => Err(ClickError::new(
                    "typed-frontend source layout does not yet support switch statements",
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
                                try_last_statement_index: try_last,
                                handler_last_statement_index: handler_last,
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
                    Ok(statement_index)
                }
                _ => {
                    let statement_index = *next_statement_index;
                    if let CStatement::Assign { name, .. }
                    | CStatement::CallAssign { target: name, .. }
                    | CStatement::Update {
                        target: CExpression::Variable(name),
                        ..
                    } = statement
                    {
                        record_assignment(layout, name, statement_index);
                    }
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
        collect_kernel_automatic_exits(function.body(), &mut layout);
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
        /// Records where the statement at `index` was written and returns
        /// that site. A labeled statement is one layout statement written
        /// where its body is; a statement with no site of its own (`break`,
        /// `continue`, `goto`, an empty statement) is named by the statement
        /// enclosing it, whose step it completes.
        fn record_site(
            layout: &mut SourceExecutionLayoutData,
            index: usize,
            mut statement: &syntax::C0Statement,
            enclosing: Option<&Site>,
        ) -> Option<Site> {
            while let syntax::C0Statement::Label {
                statement: body, ..
            } = statement
            {
                statement = body;
            }
            if syntax_statement_reads(statement) {
                layout.reads.push(index);
            }
            let site = statement
                .site()
                .and_then(syntax::C0Site::get)
                .or(enclosing)
                .cloned()?;
            layout.sites.insert(index, site.clone());
            Some(site)
        }

        /// Visits one subtree and returns the pre-order index of its last
        /// top-level statement, so an enclosing `if` can redirect its arms'
        /// control successors past the sibling arm to its own continuation.
        /// `enclosing` is the site of the nearest enclosing statement.
        fn visit(
            statement: &syntax::C0Statement,
            next_statement_index: &mut usize,
            next_loop_index: &mut usize,
            layout: &mut SourceExecutionLayoutData,
            enclosing: Option<&Site>,
        ) -> usize {
            match statement {
                syntax::C0Statement::Scope { body } => visit(
                    body,
                    next_statement_index,
                    next_loop_index,
                    layout,
                    enclosing,
                ),
                syntax::C0Statement::Seq(first, second) => {
                    visit(
                        first,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        enclosing,
                    );
                    visit(
                        second,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        enclosing,
                    )
                }
                syntax::C0Statement::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    let statement_index = *next_statement_index;
                    let own = record_site(layout, statement_index, statement, enclosing);
                    *next_statement_index += 1;
                    let then_statement_index = *next_statement_index;
                    let then_last = visit(
                        then_branch,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
                    let else_statement_index = *next_statement_index;
                    let else_last = visit(
                        else_branch,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
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
                    let own = record_site(layout, statement_index, statement, enclosing);
                    let loop_index = *next_loop_index;
                    *next_statement_index += 1;
                    *next_loop_index += 1;
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    visit(
                        body,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
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
                    let for_site = statement.site().and_then(syntax::C0Site::get).or(enclosing);
                    visit(
                        initializer,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        for_site,
                    );
                    let statement_index = *next_statement_index;
                    let own = record_site(layout, statement_index, statement, enclosing);
                    let loop_index = *next_loop_index;
                    *next_statement_index += 1;
                    *next_loop_index += 1;
                    layout.loop_bodies.insert(loop_index, *next_statement_index);
                    visit(
                        body,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
                    visit(
                        step,
                        next_statement_index,
                        next_loop_index,
                        layout,
                        own.as_ref(),
                    );
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
                    record_site(layout, statement_index, statement, enclosing);
                    if let syntax::C0Statement::Assign { name, .. }
                    | syntax::C0Statement::CallAssign { target: name, .. }
                    | syntax::C0Statement::Update {
                        target: syntax::C0Expression::Variable(name),
                        ..
                    } = statement
                    {
                        record_assignment(layout, name, statement_index);
                    }
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
            layout
                .arm_lasts_by_exited_region
                .entry(exited_if_index)
                .or_default()
                .push(last_statement_index);
            if let SourceStatementKind::If { .. } = region.kind {
                // In statement order, each statement once: what the scan of
                // every statement's list returned.
                let mut arm_lasts: Vec<usize> = layout
                    .arm_lasts_by_exited_region
                    .get(&last_statement_index)
                    .cloned()
                    .unwrap_or_default();
                arm_lasts.sort_unstable();
                arm_lasts.dedup();
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
                    None,
                );
            }
            let cycle_tail = exit_label_index.unwrap_or(statements.len());
            for statement in statements.iter().skip(1).take(cycle_tail.saturating_sub(1)) {
                visit(
                    statement,
                    &mut next_statement_index,
                    &mut next_loop_index,
                    &mut data,
                    None,
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
                    None,
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
            visit(statement, &mut 0, &mut 0, &mut data, None);
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

    /// Where the C statement at `index` was written, when it records it.
    pub(in crate::surface) fn site(
        &self,
        index: usize,
    ) -> Option<&std::sync::Arc<syntax::C0StatementSite>> {
        self.data.sites.get(&index)
    }

    pub(in crate::surface) fn execution_region_entry(
        &self,
        region: CodeRegion,
    ) -> Result<usize, String> {
        match region {
            CodeRegion::Statement(index) => Ok(index),
            CodeRegion::Loop(index) => self.loop_body_entry(index)
                .and_then(|body| body.checked_sub(1))
                .filter(|head| matches!(self.statement(*head).map(|r| r.kind), Some(SourceStatementKind::Loop { loop_index }) if loop_index == index))
                .ok_or_else(|| format!("`execute_until` cannot resolve loop({index})")),
            _ => Err("`execute_until` expects a statement or loop region".into()),
        }
    }

    pub(in crate::surface) fn assignment_entry(
        &self,
        local: &str,
        occurrence: usize,
    ) -> Result<usize, String> {
        crate::instrumentation::record_deterministic_work(1);
        self.data
            .assignments
            .get(local)
            .and_then(|entries| entries.get(occurrence))
            .copied()
            .ok_or_else(|| {
                format!("`execute_until` cannot resolve assignment({local}, {occurrence})")
            })
    }

    pub(in crate::surface) fn read_entry(&self, occurrence: usize) -> Result<usize, String> {
        crate::instrumentation::record_deterministic_work(1);
        self.data
            .reads
            .get(occurrence)
            .copied()
            .ok_or_else(|| format!("`execute_until` cannot resolve read({occurrence})"))
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
        | CExpression::CheckedObjectAddress(expression)
        | CExpression::Not(expression)
        | CExpression::Load(expression) => {
            collect_c_expression_referenced_names(expression, names);
        }
        CExpression::MemberAddress {
            object: pointer, ..
        }
        | CExpression::PointerOffsetBytes { pointer, .. }
        | CExpression::PointerAligned { pointer, .. } => {
            collect_c_expression_referenced_names(pointer, names);
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_c_expression_referenced_names(pointer, names);
        }
        crate::kernel::binary_c_expression!(left, right) => {
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
/// Typed frontends already supply kernel statements. Track their automatic
/// scope exits with the same pre-order numbering and scope rules as C syntax.
/// Root function storage belongs to the call frame; only nested scopes expire
/// here. Walking scope spines visits declarations once per containing scope.
fn collect_kernel_automatic_exits(source: &CStatement, layout: &mut SourceExecutionLayoutData) {
    fn declarations(s: &CStatement, names: &mut Vec<String>) {
        match s {
            CStatement::Declare { name, .. } | CStatement::DeclareAggregate { name, .. } => {
                names.push(name.clone())
            }
            CStatement::Seq(a, b) => {
                declarations(a, names);
                declarations(b, names);
            }
            // Implementation cleanup does not introduce a lexical scope.
            CStatement::TryCatchInt32 {
                try_body,
                cleanup_unwind: true,
                ..
            } => declarations(try_body, names),
            _ => {}
        }
    }
    fn scope(
        s: &CStatement,
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
        s: &CStatement,
        index: &mut usize,
        scopes: &mut Vec<(Vec<String>, Option<usize>)>,
        layout: &mut SourceExecutionLayoutData,
    ) -> Vec<usize> {
        if let CStatement::Scope { body } = s {
            return scope(body, index, scopes, None, layout);
        }
        if let CStatement::Seq(a, b) = s {
            visit(a, index, scopes, layout);
            return visit(b, index, scopes, layout);
        }
        let head = *index;
        *index += 1;
        match s {
            CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                let mut tails = vec![head];
                tails.extend(scope(then_branch, index, scopes, None, layout));
                tails.extend(scope(else_branch, index, scopes, None, layout));
                tails
            }
            CStatement::TryCatchInt32 {
                try_body,
                handler,
                cleanup_unwind,
                ..
            } => {
                let mut tails = vec![head];
                if *cleanup_unwind {
                    tails.extend(visit(try_body, index, scopes, layout));
                } else {
                    tails.extend(scope(try_body, index, scopes, None, layout));
                }
                tails.extend(scope(handler, index, scopes, None, layout));
                tails
            }
            CStatement::While { body, .. } => {
                scope(body, index, scopes, Some(head), layout);
                vec![head]
            }
            CStatement::Break
            | CStatement::Continue
            | CStatement::Return(_)
            | CStatement::Goto { .. } => {
                let mut names = Vec::new();
                for (declared, loop_head) in scopes.iter().rev() {
                    names.extend(declared.iter().cloned());
                    if let Some(loop_head) = loop_head
                        && matches!(s, CStatement::Break | CStatement::Continue)
                    {
                        if matches!(s, CStatement::Break) {
                            layout.automatic_break_heads.insert(head, *loop_head);
                        }
                        break;
                    }
                }
                layout.automatic_abrupt_exits.insert(head, names);
                vec![head]
            }
            // Switch is refused by the typed layout before this pass. Other
            // operations occupy one native statement and introduce no scope.
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
        if let S::Scope { body } = s {
            return scope(body, index, scopes, None, layout);
        }
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
            S::Break | S::Continue | S::Return(_, _) | S::Goto { .. } => {
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
    fn typed_automatic_scope_exits_match_c_for_nested_and_abrupt_paths() {
        for source in [
            "int32 f(int32 n) {int32 root; root=0; while(root<n) {int32 local; local=1; if(n==2) {int32 child; child=3; return child;} else {local=2;} root=root+1;} return root;}",
            "int32 f(int32 n) {int32 root; root=0; while(root<n) {int32 local; local=1; if(n==2) {int32 child; child=3; continue;} else {break;}} return root;}",
        ] {
            let function = syntax::parse_function(source).unwrap();
            let typed = function
                .clone()
                .with_prelowered_kernel_function(function.to_kernel_function());
            let c = SourceExecutionLayout::for_function(&function).unwrap();
            let native = SourceExecutionLayout::for_function(&typed).unwrap();
            assert!(!native.data.automatic_exits.is_empty());
            assert_eq!(native.data.automatic_exits, c.data.automatic_exits);
            assert_eq!(
                native.data.automatic_abrupt_exits,
                c.data.automatic_abrupt_exits
            );
            assert!(
                native
                    .data
                    .automatic_exits
                    .values()
                    .all(|names| !names.iter().any(|name| name == "root"))
            );
        }
    }

    #[test]
    fn lexical_blocks_keep_source_indexes_and_selected_lifetime_exits() {
        for source in [
            "int32 f() {int32 root; root=0; {int32 child; child=1; root=child;} return root;}",
            "int32 f() {int32 root; root=0; {int32 child; child=1; return child;} return root;}",
        ] {
            let function = syntax::parse_function(source).unwrap();
            let typed = function
                .clone()
                .with_prelowered_kernel_function(function.to_kernel_function());
            let c = SourceExecutionLayout::for_function(&function).unwrap();
            let native = SourceExecutionLayout::for_function(&typed).unwrap();
            assert_eq!(native.data.statements.len(), c.data.statements.len());
            assert_eq!(native.data.automatic_exits, c.data.automatic_exits);
            assert_eq!(
                native.data.automatic_abrupt_exits,
                c.data.automatic_abrupt_exits
            );
            assert!(
                native
                    .data
                    .automatic_exits
                    .values()
                    .any(|names| names.iter().any(|name| name == "child"))
            );
            assert!(
                native
                    .data
                    .automatic_exits
                    .values()
                    .all(|names| names.iter().all(|name| name != "root"))
            );
        }
    }

    #[test]
    fn read_frontiers_index_loads_and_ignore_address_computation() {
        let function = syntax::parse_function(
            "int32 f(int32* p, int32** pp) {int32 x;int32* q; q=&*p; x=*p; q=&**pp; return *p;}",
        )
        .unwrap();
        let typed = function
            .clone()
            .with_prelowered_kernel_function(function.to_kernel_function());
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            assert_eq!(layout.data.reads.len(), 3);
            assert!(layout.read_entry(0).unwrap() < layout.read_entry(1).unwrap());
            assert!(layout.read_entry(3).is_err());
        }
        assert!(!expression_reads(&CExpression::AddressOf(Box::new(
            CExpression::Variable("x".into())
        ))));
    }

    #[test]
    fn read_frontiers_have_linear_expression_work_and_indexed_lookups() {
        for count in [8, 128, 1024] {
            let mut source = String::from("int32 f(const int32* p) {int32 x; int32 other;");
            for _ in 0..count {
                source.push_str("other=1;x=*p+other;");
            }
            source.push_str("return x;}");
            let function = syntax::parse_function(&source).unwrap();
            let typed = function
                .clone()
                .with_prelowered_kernel_function(function.to_kernel_function());
            for function in [&function, &typed] {
                let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
                    SourceExecutionLayout::for_function(function).unwrap()
                });
                assert_eq!(layout.data.reads.len(), count);
                assert!(work < 16 * count, "{count} reads: {work}");
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for n in 0..count {
                        layout.read_entry(n).unwrap();
                    }
                });
                assert_eq!(work, count);
            }
        }
    }

    #[test]
    fn assignment_frontiers_index_static_stores_in_both_layouts() {
        let function = syntax::parse_function("int32 f(int32 n) { int32 x; x=0; if(n==0) {x=1;} else {x=2;} while(x<3) {x=3;} x+=1; x++; return x; }").unwrap();
        let kernel = function.to_kernel_function();
        let typed = function.clone().with_prelowered_kernel_function(kernel);
        for function in [&function, &typed] {
            let layout = SourceExecutionLayout::for_function(function).unwrap();
            let indices: Vec<_> = (0..6)
                .map(|n| layout.assignment_entry("x", n).unwrap())
                .collect();
            assert!(indices.windows(2).all(|pair| pair[0] < pair[1]));
            assert!(layout.assignment_entry("x", 6).is_err());
            assert!(layout.assignment_entry("absent", 0).is_err());
        }
    }

    #[test]
    fn assignment_frontiers_build_and_resolve_without_scanning_unrelated_stores() {
        for count in [8, 128, 1024] {
            let mut source = String::from("int32 f() {int32 marker; int32 unrelated;");
            for i in 0..count {
                source.push_str(&format!("unrelated={i};marker={i};"));
            }
            source.push_str("return marker;}");
            let function = syntax::parse_function(&source).unwrap();
            let kernel = function.to_kernel_function();
            let typed = function.clone().with_prelowered_kernel_function(kernel);
            for function in [&function, &typed] {
                let (layout, work) = crate::instrumentation::measure_deterministic_work(|| {
                    SourceExecutionLayout::for_function(function).unwrap()
                });
                assert!(work <= 8 * count, "{count} stores: {work}");
                assert_eq!(layout.data.assignments["marker"].len(), count);
                let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                    for occurrence in 0..count {
                        layout.assignment_entry("marker", occurrence).unwrap();
                    }
                });
                assert_eq!(work, count);
            }
        }
    }

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
                assignments: BTreeMap::new(),
                reads: Vec::new(),
                automatic_exits: BTreeMap::new(),
                automatic_abrupt_exits: BTreeMap::new(),
                automatic_break_heads: BTreeMap::new(),
                loop_bodies: BTreeMap::new(),
                natural_loop_targets: BTreeMap::new(),
                natural_exit_targets: BTreeMap::new(),
                natural_exit_statement_indices: BTreeMap::new(),
                exited_branch_regions: BTreeMap::new(),
                arm_lasts_by_exited_region: BTreeMap::new(),
                sites: BTreeMap::new(),
            }),
        };
        let cloned = layout.clone();

        assert!(std::sync::Arc::ptr_eq(&layout.data, &cloned.data));
        assert_eq!(cloned.data.statements.len(), 4096);
        assert_eq!(
            cloned
                .statement(4095)
                .map(|region| region.continuation_node),
            Some(4096)
        );
    }
}
