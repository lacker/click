use super::*;
// Staged common fold readers; producers activate after the Surface boundary.
#[allow(dead_code)]
mod retained_folds;
#[allow(dead_code)]
mod retained_matches;
#[allow(dead_code)]
mod retained_pointers;
use crate::kernel::spec::walk::{SpecNode, Visit, WalkBudget, walk_spec};

/// Visit only the carrier-bearing leaves of shared machine arithmetic.
/// Conversion payloads and registered loads keep each collector's existing
/// scope rules; arithmetic nodes themselves introduce no variables or binders.
fn visit_machine_carrier_leaves(
    machine: &SharedMachineIntegerTerm,
    visit: impl FnMut(MachineOperandView<'_>),
) {
    visit_machine_operand_carrier_leaves(machine.operand_view(), visit);
}

fn visit_machine_operand_carrier_leaves(
    operand: MachineOperandView<'_>,
    visit: impl FnMut(MachineOperandView<'_>),
) {
    visit_machine_operand_carrier_leaves_selected(operand, true, visit);
}

fn visit_machine_operand_carrier_leaves_selected(
    operand: MachineOperandView<'_>,
    include_variables: bool,
    mut visit: impl FnMut(MachineOperandView<'_>),
) {
    let MachineOperandView::Shared(root) = operand else {
        visit(operand);
        return;
    };
    // A root atom needs no DAG summary. Keep the native collector's one-leaf
    // cost, including its current registry and state handling.
    if let Some(variable) = operand.variable() {
        if !include_variables {
            return;
        }
        visit(MachineOperandView::Legacy(&MachineTerm::Variable(
            *variable,
        )));
        return;
    }
    if operand.read().is_some() {
        visit(operand);
        return;
    }
    if operand.literal().is_some() {
        return;
    }
    if matches!(
        root.node(),
        KernelTermNode::Fold(_) | KernelTermNode::Match(_) | KernelTermNode::FloatConvert { .. }
    ) {
        visit(operand);
        return;
    }
    if let Some(leaf) = root.machine_conversion_leaf() {
        visit(MachineOperandView::Legacy(leaf));
        return;
    }
    if let Some(leaves) =
        shared_machine_conversion_leaves(root, || !checked_collection_checkpoint())
    {
        for (_, leaf) in leaves.iter() {
            if checked_collection_checkpoint() {
                return;
            }
            if matches!(
                leaf.node(),
                KernelTermNode::Fold(_)
                    | KernelTermNode::Match(_)
                    | KernelTermNode::FloatConvert { .. }
            ) {
                visit(MachineOperandView::Shared(leaf));
            } else {
                visit(MachineOperandView::Legacy(
                    leaf.machine_conversion_leaf().expect("conversion leaf"),
                ));
            }
        }
    }
    if let Some(reads) = shared_machine_read_leaves(root, || !checked_collection_checkpoint()) {
        for (_, read) in reads.iter() {
            if checked_collection_checkpoint() {
                return;
            }
            visit(MachineOperandView::Shared(read));
        }
    }
    if !include_variables {
        return;
    }
    if let Some(written) =
        shared_machine_syntax_variables(root, || !checked_collection_checkpoint())
    {
        for variable in written.iter() {
            if checked_collection_checkpoint() {
                return;
            }
            visit(MachineOperandView::Legacy(&MachineTerm::Variable(
                *variable,
            )));
        }
    }
}

/// Existing native leaf collectors can inspect a selected read descriptor or
/// opaque leaf without expanding the surrounding shared arithmetic DAG.
/// Each collector retains its own registry, state and binder rules.
pub(in crate::kernel) fn visit_machine_operand_scoped_leaves(
    operand: MachineOperandView<'_>,
    visit: impl FnMut(MachineOperandView<'_>),
) {
    visit_machine_operand_carrier_leaves_selected(operand, false, visit);
}

/// The machine-variable collector's existing carrier rules on a retained
/// operand. Written arithmetic contributes only its distinct variables and
/// conversion leaves; registered loads are resolved in the current query.
pub(in crate::kernel) fn collect_machine_bitvector_variables(
    machine: &SharedMachineIntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    visit_machine_carrier_leaves(machine, |leaf| {
        collect_operand_bitvector_variables(leaf, variables);
    });
}

fn collect_machine_integer_variables(
    machine: &SharedMachineIntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    // Distinct conversions may share a large Integer payload. Keep one seen
    // set for the whole machine operand, as the native traversal does.
    let mut seen = SeenTerms::default();
    visit_machine_carrier_leaves(machine, |leaf| {
        collect_operand_integer_variables_seen(leaf, variables, &mut seen);
    });
}

fn collect_operand_bitvector_variables(
    operand: MachineOperandView<'_>,
    variables: &mut BTreeSet<Variable>,
) {
    if let MachineOperandView::Shared(root) = operand
        && matches!(root.node(), KernelTermNode::FloatConvert { .. })
    {
        variables.extend(
            retained_folds::common_variables(
                root,
                retained_folds::FoldVariableRead::ExpressionFree,
                &mut Default::default(),
            )
            .iter()
            .copied(),
        );
        return;
    }
    if let MachineOperandView::Shared(root) = operand
        && let KernelTermNode::Match(fold) = root.node()
    {
        retained_matches::collect_match_variables(
            fold,
            retained_folds::FoldVariableRead::ExpressionFree,
            variables,
        );
        return;
    }
    if let MachineOperandView::Shared(root) = operand
        && let KernelTermNode::Fold(fold) = root.node()
    {
        retained_folds::collect_fold_variables(
            fold,
            retained_folds::FoldVariableRead::ExpressionFree,
            variables,
        );
        return;
    }
    if let Some((memory, pointer, _)) = operand.read() {
        collect_shared_memory_bitvector_variables(memory, variables);
        collect_pointer_bitvector_variables(pointer, variables);
        collect_stored_load_connection_variables(memory, pointer, variables);
    } else if let MachineOperandView::Legacy(term) = operand {
        collect_bitvector_variables(term, variables);
    } else {
        unreachable!("carrier leaf");
    }
}

fn collect_operand_integer_variables_seen(
    operand: MachineOperandView<'_>,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if let MachineOperandView::Shared(root) = operand
        && matches!(root.node(), KernelTermNode::FloatConvert { .. })
    {
        variables.extend(
            retained_folds::common_variables(
                root,
                retained_folds::FoldVariableRead::IntegerFree,
                &mut Default::default(),
            )
            .iter()
            .copied(),
        );
        return;
    }
    if let MachineOperandView::Shared(root) = operand
        && let KernelTermNode::Match(fold) = root.node()
    {
        retained_matches::collect_match_variables(
            fold,
            retained_folds::FoldVariableRead::IntegerFree,
            variables,
        );
        return;
    }
    if let MachineOperandView::Shared(root) = operand
        && let KernelTermNode::Fold(fold) = root.node()
    {
        retained_folds::collect_fold_variables(
            fold,
            retained_folds::FoldVariableRead::IntegerFree,
            variables,
        );
        return;
    }
    if let Some((_, pointer, _)) = operand.read() {
        collect_pointer_integer_variables(pointer, variables, seen);
    } else if let MachineOperandView::Legacy(term) = operand {
        collect_bitvector_integer_variables_seen(term, variables, seen);
    } else {
        unreachable!("carrier leaf");
    }
}

fn collect_operand_binder_variables_seen(
    operand: MachineOperandView<'_>,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if let MachineOperandView::Shared(root) = operand
        && matches!(root.node(), KernelTermNode::FloatConvert { .. })
    {
        integer_variables.extend(
            retained_folds::common_variables(
                root,
                retained_folds::FoldVariableRead::IntegerBinders,
                &mut Default::default(),
            )
            .iter()
            .copied(),
        );
        bitvector_variables.extend(
            retained_folds::common_variables(
                root,
                retained_folds::FoldVariableRead::MachineBinders,
                &mut Default::default(),
            )
            .iter()
            .copied(),
        );
        return;
    }
    if let MachineOperandView::Shared(root) = operand
        && let KernelTermNode::Match(fold) = root.node()
    {
        retained_matches::collect_match_variables(
            fold,
            retained_folds::FoldVariableRead::IntegerBinders,
            integer_variables,
        );
        retained_matches::collect_match_variables(
            fold,
            retained_folds::FoldVariableRead::MachineBinders,
            bitvector_variables,
        );
        return;
    }
    if let MachineOperandView::Shared(root) = operand
        && let KernelTermNode::Fold(fold) = root.node()
    {
        retained_folds::collect_fold_variables(
            fold,
            retained_folds::FoldVariableRead::IntegerBinders,
            integer_variables,
        );
        retained_folds::collect_fold_variables(
            fold,
            retained_folds::FoldVariableRead::MachineBinders,
            bitvector_variables,
        );
        return;
    }
    // The existing binder collector treats read addresses as binder-free.
    if operand.read().is_some() {
        return;
    }
    if let MachineOperandView::Legacy(term) = operand {
        collect_bitvector_binder_variables_seen(term, integer_variables, bitvector_variables, seen);
    } else {
        unreachable!("carrier leaf");
    }
}

#[derive(Default)]
struct SeenTerms {
    integers: BTreeSet<u64>,
    pointers: BTreeSet<u64>,
}
impl SeenTerms {
    fn insert(&mut self, id: u64) -> bool {
        self.integers.insert(id)
    }
}

thread_local! {
    static CONNECTION_BLOCKS: std::cell::RefCell<Option<BTreeSet<AddressBase>>> = const { std::cell::RefCell::new(None) };
}

/// Explicit values and addresses a fact names; state contents are not
/// dependencies merely because two propositions carry the same state.
pub(crate) fn collect_atomic_connection_keys(
    proposition: &Proposition,
) -> BTreeSet<AtomicConnectionKey> {
    struct Scope(Option<BTreeSet<AddressBase>>);
    impl Drop for Scope {
        fn drop(&mut self) {
            CONNECTION_BLOCKS.with(|blocks| *blocks.borrow_mut() = self.0.take());
        }
    }
    let prior = CONNECTION_BLOCKS.with(|blocks| blocks.replace(Some(BTreeSet::new())));
    let _scope = Scope(prior);
    let mut variables = BTreeSet::new();
    collect_proposition_connection_variables(proposition, &mut variables);
    let mut keys = variables
        .into_iter()
        .map(AtomicConnectionKey::Variable)
        .collect::<BTreeSet<_>>();
    CONNECTION_BLOCKS.with(|blocks| {
        keys.extend(
            blocks
                .borrow()
                .as_ref()
                .unwrap()
                .iter()
                .cloned()
                .map(AtomicConnectionKey::Block),
        )
    });
    keys
}

thread_local! {
    static CONNECTION_VARIABLES: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static CONNECTION_LOAD_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn collecting_connection_variables() -> bool {
    CONNECTION_VARIABLES.with(std::cell::Cell::get)
}

/// How far back along a state's derivation
/// [`collect_proposition_frame_variables`] looks for havoc ranges.
const HAVOC_RANGE_HOPS: usize = 64;

thread_local! {
    static COLLECTING_HAVOC_RANGES: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    // Observation origins can lead back to a state whose havoc bounds
    // contain this same read. Each root contributes its bounded range walk
    // once to the current planner collection, including cyclic origins.
    static FRAME_STATES: std::cell::RefCell<std::collections::HashSet<(u32, u32)>> = Default::default();
    /// Set while [`execution_variable_ceiling`] collects: an interned
    /// state then contributes only its greatest remembered variable below
    /// the execution ceiling, which is all a ceiling needs.
    static EXECUTION_CEILING_ONLY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// The greatest variable of the execution range
/// (`ExecutionBudget::KERNEL_VARIABLE_BASE` up to its ceiling) that
/// `proposition` mentions: what an execution must allocate above for a fresh
/// identity to name nothing the fact names. It collects as
/// [`collect_proposition_bitvector_variables`] does, with every state in
/// full and no collection mode of the caller's in force, except that a
/// state contributes only its greatest remembered variable.
pub(in crate::kernel) fn proposition_execution_variable_ceiling(
    proposition: &Proposition,
) -> Option<Variable> {
    execution_variable_ceiling(None, |variables| {
        collect_proposition_bitvector_variables(proposition, variables)
    })
    .0
}

/// [`proposition_execution_variable_ceiling`] for a condition fact.
pub(in crate::kernel) fn condition_execution_variable_ceiling(
    condition: &ConditionTerm,
) -> Option<Variable> {
    execution_variable_ceiling(None, |variables| {
        collect_condition_bitvector_variables(condition, variables)
    })
    .0
}

/// The ceiling of `proposition`'s written syntax, stopping at each state,
/// and whether it met one: filing a fact reads syntax, never state
/// contents, so a fact that names a state has its whole ceiling taken
/// later, when an execution asks for it.
///
/// A composition fact names a whole resource context, and every step states
/// several; its ceiling is the held facts' combined ceiling, read from the
/// context's cached canonical fact set instead of walking every fact.
pub(in crate::kernel) fn proposition_syntax_execution_variable_ceiling(
    proposition: &Proposition,
) -> (Option<Variable>, bool) {
    if let Proposition::ResourceComposition(resources) = proposition {
        return resources.syntax_ceiling(resource_fact_syntax_execution_variable_ceiling);
    }
    execution_variable_ceiling(Some(false), |variables| {
        collect_proposition_bitvector_variables(proposition, variables)
    })
}

/// [`proposition_syntax_execution_variable_ceiling`] for one held resource
/// fact of a composition.
fn resource_fact_syntax_execution_variable_ceiling(
    fact: &ResourceFact,
) -> (Option<Variable>, bool) {
    execution_variable_ceiling(Some(false), |variables| {
        collect_resource_fact_bitvector_variables(fact, variables)
    })
}

/// [`proposition_syntax_execution_variable_ceiling`] for a condition fact.
pub(in crate::kernel) fn condition_syntax_execution_variable_ceiling(
    condition: &ConditionTerm,
) -> (Option<Variable>, bool) {
    execution_variable_ceiling(Some(false), |variables| {
        collect_condition_bitvector_variables(condition, variables)
    })
}

/// Collects for a ceiling with every caller mode cleared; `deferral` is
/// `Some(false)` to stop at states, and the second result says whether
/// one was met.
pub(in crate::kernel) fn execution_variable_ceiling(
    deferral: Option<bool>,
    collect: impl FnOnce(&mut BTreeSet<Variable>),
) -> (Option<Variable>, bool) {
    struct Restore(bool, bool, bool, Option<bool>);
    impl Drop for Restore {
        fn drop(&mut self) {
            EXECUTION_CEILING_ONLY.with(|flag| flag.set(self.0));
            CONNECTION_VARIABLES.with(|flag| flag.set(self.1));
            COLLECTING_HAVOC_RANGES.with(|flag| flag.set(self.2));
            DEFER_CONDITION_STATES.with(|state| state.set(self.3));
        }
    }
    let _restore = Restore(
        EXECUTION_CEILING_ONLY.with(|flag| flag.replace(true)),
        CONNECTION_VARIABLES.with(|flag| flag.replace(false)),
        COLLECTING_HAVOC_RANGES.with(|flag| flag.replace(false)),
        DEFER_CONDITION_STATES.with(|state| state.replace(deferral)),
    );
    let mut variables = BTreeSet::new();
    collect(&mut variables);
    let ceiling = variables
        .range(
            Variable(crate::kernel::ExecutionBudget::KERNEL_VARIABLE_BASE)
                ..Variable(crate::kernel::ExecutionBudget::KERNEL_VARIABLE_CEILING),
        )
        .next_back()
        .copied();
    (
        ceiling,
        DEFER_CONDITION_STATES.with(|state| state.get() == Some(true)),
    )
}

/// The bitvector variables of `proposition`, with those of the ranges the
/// calls and loops recently behind each state it loads from wrote.
///
/// Like [`collect_proposition_connection_variables`], this is for a planner
/// choosing which facts a derivation may need.
pub(crate) fn collect_proposition_frame_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    struct Scope(bool, std::collections::HashSet<(u32, u32)>);
    impl Drop for Scope {
        fn drop(&mut self) {
            COLLECTING_HAVOC_RANGES.with(|flag| flag.set(self.0));
            FRAME_STATES.with(|seen| *seen.borrow_mut() = std::mem::take(&mut self.1));
        }
    }
    let _scope = Scope(
        COLLECTING_HAVOC_RANGES.with(|flag| flag.replace(true)),
        FRAME_STATES.with(|seen| std::mem::take(&mut *seen.borrow_mut())),
    );
    collect_proposition_connection_variables(proposition, variables);
}

/// Every variable through which `proposition` can be related to another
/// fact: its bitvector variables, and also the algebraic-value and
/// pointer-offset variables the bitvector collectors deliberately leave out.
///
/// This is for a planner choosing which facts a derivation may need. It is
/// not a free-variable set for freshness or substitution.
pub(crate) fn collect_proposition_connection_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    struct Scope(bool);
    impl Drop for Scope {
        fn drop(&mut self) {
            CONNECTION_VARIABLES.with(|flag| flag.set(self.0));
        }
    }
    let _scope = Scope(CONNECTION_VARIABLES.with(|flag| flag.replace(true)));
    collect_proposition_bitvector_variables(proposition, variables);
}

pub(in crate::kernel) fn bitvector_same_base_nonzero_const_offset(
    left: &MachineTerm,
    right: &MachineTerm,
) -> bool {
    if let Some((left_base, left_addend)) = left.add_const_parts() {
        if &left_base == right {
            return left_addend != 0;
        }
        if let Some((right_base, right_addend)) = right.add_const_parts() {
            return left_base == right_base && left_addend != right_addend;
        }
    }

    if let Some((right_base, right_addend)) = right.add_const_parts() {
        return &right_base == left && right_addend != 0;
    }

    false
}

pub(crate) fn collect_proposition_bitvector_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    let mut depth = 0;
    let mut current = proposition;
    while let Proposition::Implies(_, body) = current {
        depth += 1;
        current = body;
    }
    if depth > 128 {
        let mut pending = vec![proposition];
        while let Some(proposition) = pending.pop() {
            match proposition {
                Proposition::And(left, right)
                | Proposition::Or(left, right)
                | Proposition::Implies(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
                Proposition::Not(body)
                | Proposition::ForAll { body, .. }
                | Proposition::Exists { body, .. } => pending.push(body),
                proposition => collect_proposition_bitvector_variables_one(proposition, variables),
            }
        }
        return;
    }
    collect_proposition_bitvector_variables_one(proposition, variables);
}

fn collect_proposition_bitvector_variables_one(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    match proposition {
        Proposition::VolatileAccess(event) => {
            collect_pointer_bitvector_variables(&event.pointer, variables);
            collect_expression_value_bitvector_variables(event.value.value(), variables);
        }
        Proposition::Equal(left, right) => {
            collect_term_bitvector_variables(left, variables);
            collect_term_bitvector_variables(right, variables);
        }
        Proposition::ConditionIs(condition, _) => {
            retained_folds::collect_boolean_variables(
                condition.operand_view(),
                retained_folds::FoldVariableRead::ExpressionFree,
                variables,
            );
        }
        Proposition::Predicate { arguments, .. } => {
            for argument in arguments {
                collect_term_bitvector_variables(argument, variables);
            }
        }
        Proposition::ProgramExpressionEvaluates {
            state,
            expression,
            outcome,
        } => {
            collect_execution_state_bitvector_variables(state, variables);
            collect_program_expression_bitvector_variables(expression, variables);
            collect_program_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::ProgramConditionEvaluates {
            state, condition, ..
        } => {
            collect_execution_state_bitvector_variables(state, variables);
            collect_program_expression_bitvector_variables(condition, variables);
        }
        Proposition::ProgramStatementVerifies {
            state,
            statement,
            outcome,
        } => {
            collect_execution_state_bitvector_variables(state, variables);
            collect_execution_statement_bitvector_variables(statement, variables);
            collect_execution_statement_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::ProgramFunctionVerifies {
            state,
            arguments,
            function,
            outcome,
        } => {
            collect_execution_state_bitvector_variables(state, variables);
            for argument in arguments {
                collect_program_expression_bitvector_variables(argument, variables);
            }
            collect_program_function_bitvector_variables(function, variables);
            collect_program_function_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::ProgramFunctionPartiallySatisfiesSpecification {
            function,
            specification,
        } => {
            collect_program_function_bitvector_variables(function, variables);
            collect_program_function_specification_bitvector_variables(specification, variables);
        }
        Proposition::MemoryLoads {
            memory,
            pointer,
            outcome,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
            collect_program_expression_outcome_bitvector_variables(outcome, variables);
        }
        Proposition::MemoryReadDefined {
            memory, pointer, ..
        }
        | Proposition::MemoryCanStore {
            memory, pointer, ..
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(pointer, variables);
        }
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide: _,
        } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_pointer_bitvector_variables(base, variables);
            collect_expression_value_bitvector_variables(bytes.value(), variables);
        }
        Proposition::ResourceSeparate { left, right } => {
            collect_resource_bitvector_variables(left, variables);
            collect_resource_bitvector_variables(right, variables);
        }
        Proposition::ResourceComposition(resources) => {
            collect_resource_context_bitvector_variables(resources, variables);
        }
        Proposition::ResourceViewable { memory, resource } => {
            collect_memory_bitvector_variables(memory, variables);
            collect_resource_bitvector_variables(resource, variables);
        }
        Proposition::ResourceContains { parent, child } => {
            collect_resource_bitvector_variables(parent, variables);
            collect_resource_bitvector_variables(child, variables);
        }
        Proposition::MemoryMutatesOnly {
            before,
            after,
            writes,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for (pointer, _) in writes {
                collect_pointer_bitvector_variables(pointer, variables);
            }
        }
        Proposition::MemoryEffectSummary {
            before,
            after,
            mutable_ranges,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            for range in mutable_ranges {
                collect_memory_range_bitvector_variables(range, variables);
            }
        }
        Proposition::HeapAllocationFreed {
            before,
            after,
            allocation_base,
            bytes,
        } => {
            collect_memory_bitvector_variables(before, variables);
            collect_memory_bitvector_variables(after, variables);
            collect_pointer_bitvector_variables(allocation_base, variables);
            collect_bitvector_variables(bytes.bytes(), variables);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_proposition_bitvector_variables(left, variables);
            collect_proposition_bitvector_variables(right, variables);
        }
        Proposition::Not(body) => collect_proposition_bitvector_variables(body, variables),
        Proposition::ForAll { var, body, .. } | Proposition::Exists { var, body, .. } => {
            collect_proposition_bitvector_variables(body, variables);
            variables.remove(var);
        }
    }
}

pub(in crate::kernel) fn collect_term_bitvector_variables(
    term: &Term,
    variables: &mut BTreeSet<Variable>,
) {
    match term {
        Term::Condition(condition) => collect_condition_bitvector_variables(condition, variables),
        Term::Bitvector32(bits) => collect_bitvector_variables(bits, variables),
        Term::Integer(integer) => collect_integer_variables(integer, variables),
        Term::PointerOffset(offset) => {
            collect_pointer_offset_bitvector_variables(offset, variables)
        }
        Term::ProgramValue(value) => collect_program_value_bitvector_variables(value, variables),
        Term::Sequence(sequence) => collect_sequence_bitvector_variables(sequence, variables),
        Term::Algebraic(term) => collect_algebraic_term_bitvector_variables(term, variables),
        Term::Memory(memory) => collect_memory_bitvector_variables(memory, variables),
        Term::ExecutionState(state) => {
            collect_execution_state_bitvector_variables(state, variables)
        }
    }
}

/// A condition inside an algebraic conditional, carried as the scalar
/// conditional `if condition { 1 } else { 0 }`: a walker reaches its terms as
/// it reaches any scalar conditional's.
fn condition_carrier(condition: &ConditionTerm) -> AlgebraicValue {
    AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::If {
        condition: Box::new(condition.clone()),
        then_term: Box::new(MachineTerm::constant(1)),
        else_term: Box::new(MachineTerm::constant(0)),
    }))
}

/// A [`AlgebraicTermNode::MemoryLoad`]'s memory and address as the scalar
/// load at them: a walker reaches them as it reaches a scalar load's.
fn load_carrier(
    memory: &crate::kernel::SharedMemory,
    pointer: &crate::kernel::Address,
) -> AlgebraicValue {
    AlgebraicValue::Program(ProgramValue::UInt64(
        AlgebraicTermNode::memory_load_carrier(&crate::kernel::ProgramPoint::at(memory), pointer),
    ))
}

fn collect_algebraic_term_bitvector_variables(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => {
            if collecting_connection_variables() {
                variables.insert(*variable);
            }
        }
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_bitvector_variables(field, variables);
            }
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_algebraic_value_bitvector_variables(
                &load_carrier(memory.shared_memory(), pointer),
                variables,
            );
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_algebraic_value_bitvector_variables(&condition_carrier(condition), variables);
            collect_algebraic_term_bitvector_variables(then_term, variables);
            collect_algebraic_term_bitvector_variables(else_term, variables);
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_term_bitvector_variables(scrutinee, variables);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bitvector_variables(binding, variables);
                }
                collect_algebraic_term_bitvector_variables(&arm.body, variables);
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                match argument {
                    PureFunctionArgument::SharedMachine(value) => {
                        collect_machine_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_program_value_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_term_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Integer(value) => {
                        collect_integer_variables(value, variables)
                    }
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bitvector_variables(memory, variables);
                        collect_program_value_bitvector_variables(pointer, variables);
                    }
                }
            }
        }
    }
}

fn collect_algebraic_value_bitvector_variables<'a>(
    value: impl Into<ResourceFieldValue<'a>>,
    variables: &mut BTreeSet<Variable>,
) {
    match value.into() {
        ResourceFieldValue::Program(value) => {
            collect_program_value_bitvector_variables(value, variables)
        }
        ResourceFieldValue::Integer(value) => collect_integer_variables(value, variables),
        ResourceFieldValue::Algebraic(value) => {
            collect_algebraic_term_bitvector_variables(value, variables)
        }
    }
}

fn collect_sequence_bitvector_variables(
    sequence: &SequenceTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match sequence.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for index in 0..values.len() {
                if let Some(value) = values.retained_value_ref(index) {
                    collect_expression_value_bitvector_variables(value, variables);
                } else {
                    collect_program_value_bitvector_variables(
                        values.get(index).unwrap(),
                        variables,
                    );
                }
            }
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_bitvector_variables(left, variables);
            collect_sequence_bitvector_variables(right, variables);
        }
    }
}

pub(in crate::kernel) fn collect_program_expression_bitvector_variables(
    expression: &ProgramExpression,
    variables: &mut BTreeSet<Variable>,
) {
    match expression {
        ProgramExpression::Value(value) => {
            collect_program_value_bitvector_variables(value, variables)
        }
        ProgramExpression::Variable(_)
        | ProgramExpression::StringLiteral(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Cast { expression, .. } => {
            collect_program_expression_bitvector_variables(expression, variables)
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_program_expression_bitvector_variables(field, variables);
            }
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_bitvector_variables(condition, variables);
            collect_program_expression_bitvector_variables(then_branch, variables);
            collect_program_expression_bitvector_variables(else_branch, variables);
        }
        ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        } => collect_program_expression_bitvector_variables(expression, variables),
        ProgramExpression::AddressOf(body)
        | ProgramExpression::CheckedObjectAddress(body)
        | ProgramExpression::Not(body)
        | ProgramExpression::Load(body) => {
            collect_program_expression_bitvector_variables(body, variables);
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            collect_program_expression_bitvector_variables(pointer, variables);
        }
        ProgramExpression::TypedLoad { pointer, .. } => {
            collect_program_expression_bitvector_variables(pointer, variables);
        }
        crate::kernel::binary_c_expression!(left, right) => {
            collect_program_expression_bitvector_variables(left, variables);
            collect_program_expression_bitvector_variables(right, variables);
        }
        ProgramExpression::BitwiseNot(expression) => {
            collect_program_expression_bitvector_variables(expression, variables);
        }
    }
}

pub(in crate::kernel) fn collect_execution_statement_bitvector_variables(
    statement: &ProgramStatement,
    variables: &mut BTreeSet<Variable>,
) {
    match statement {
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::Skip
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::DeclareAggregate { .. } => {}

        ProgramStatement::Declare {
            initializer,
            zero_fill,
            ..
        } => {
            for expression in initializer
                .iter()
                .chain(zero_fill.iter().flat_map(ZeroFill::expressions))
            {
                collect_program_expression_bitvector_variables(expression, variables);
            }
        }
        ProgramStatement::Assign { expression, .. }
        | ProgramStatement::Return(expression)
        | ProgramStatement::Throw(expression)
        | ProgramStatement::Assert {
            condition: expression,
            ..
        }
        | ProgramStatement::LoopTest {
            condition: expression,
            ..
        }
        | ProgramStatement::StepValue { expression, .. } => {
            collect_program_expression_bitvector_variables(expression, variables);
        }
        ProgramStatement::CallConstruct { arguments, .. } => {
            for argument in arguments {
                collect_program_expression_bitvector_variables(argument, variables);
            }
        }
        ProgramStatement::Call { arguments, .. }
        | ProgramStatement::CallResult { arguments, .. } => {
            for argument in arguments {
                collect_program_expression_bitvector_variables(argument, variables);
            }
        }
        ProgramStatement::HeapAllocate { bytes, .. } => {
            collect_program_expression_bitvector_variables(bytes, variables);
        }
        ProgramStatement::HeapFree { pointer } => {
            collect_program_expression_bitvector_variables(pointer, variables);
        }
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                collect_execution_statement_bitvector_variables(statement, variables);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => {
            collect_execution_statement_bitvector_variables(try_body, variables);
            collect_execution_statement_bitvector_variables(handler, variables);
        }
        ProgramStatement::Store { pointer, value } => {
            collect_program_expression_bitvector_variables(pointer, variables);
            collect_program_expression_bitvector_variables(value, variables);
        }
        ProgramStatement::TypedStore { pointer, value, .. } => {
            collect_program_expression_bitvector_variables(pointer, variables);
            collect_program_expression_bitvector_variables(value, variables);
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => {
            collect_program_expression_bitvector_variables(target, variables);
            collect_program_expression_bitvector_variables(source, variables);
        }
        ProgramStatement::Update {
            target, operand, ..
        } => {
            collect_program_expression_bitvector_variables(target, variables);
            collect_program_expression_bitvector_variables(operand, variables);
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_bitvector_variables(condition, variables);
            collect_execution_statement_bitvector_variables(then_branch, variables);
            collect_execution_statement_bitvector_variables(else_branch, variables);
        }
        ProgramStatement::Loop {
            test: loop_test,
            update,
            invariant,
            invariant_checks,
            effect_checks,
            ranking_measures,
            body,
            ..
        } => {
            let condition = loop_test.source_condition();
            let test = loop_test.source_region();
            if let Some(condition) = condition {
                collect_program_expression_bitvector_variables(condition, variables);
            }
            for proposition in invariant {
                collect_proposition_bitvector_variables(proposition, variables);
            }
            for check in invariant_checks {
                collect_spec_proposition_bitvector_variables(check.proposition(), variables);
            }
            for check in effect_checks {
                collect_loop_effect_bitvector_variables(check.effect(), variables);
            }
            // A `decreases` component is read at the loop head like an
            // invariant is, and substitution rewrites it like one, so the
            // variables it already names are reserved like an invariant
            // check's. Skipping them would let a fresh execution variable be
            // handed out with a name the measure already uses.
            for measure in ranking_measures {
                collect_ranking_component_variables(measure, variables);
            }
            collect_execution_statement_bitvector_variables(body, variables);
            if let Some(test) = test {
                collect_execution_statement_bitvector_variables(&test.statement, variables);
            }
            if let Some(update) = update {
                collect_execution_statement_bitvector_variables(update, variables);
            }
        }
        ProgramStatement::Switch { expression, cases } => {
            collect_program_expression_bitvector_variables(expression, variables);
            for case in cases {
                collect_execution_statement_bitvector_variables(&case.body, variables);
            }
        }
    }
}

/// The variables one declared `decreases` component already names.
///
/// A component is read at the states the kernel picks and substitution
/// rewrites it, so its variables are reserved wherever it travels: on a loop
/// head, and on the recursion anchor of the function that declared it.
pub(in crate::kernel) fn collect_ranking_component_variables(
    component: &RankingComponent,
    variables: &mut BTreeSet<Variable>,
) {
    match component {
        RankingComponent::ProgramExpression(expression) => {
            collect_program_expression_bitvector_variables(expression, variables);
        }
        RankingComponent::Pure { expression, .. } => {
            collect_spec_expression_bitvector_variables(expression, variables);
        }
        RankingComponent::PureInteger { expression, .. } => {
            collect_spec_integer_variables(expression, variables);
        }
    }
}

/// Collects the free variables of a specification subtree, for premise
/// indexing.
///
/// A quantifier's variable is removed once its body is collected; fold and
/// match binders are kept. Arguments of every application result type are
/// visited, including mathematical Integer arguments. A specification memory is an execution
/// state: its blocks and cells are opaque to lexical variable collection,
/// and only the explicit pointer and expression payloads beside it are
/// visited.
fn collect_spec_bitvector_variables(root: SpecNode<'_>, variables: &mut BTreeSet<Variable>) {
    walk_spec::<()>(root, WalkBudget::Unmetered, |node| {
        use SpecNode as N;
        match node {
            N::Resource(SpecResource::Value(resource)) => {
                collect_resource_bitvector_variables(resource, variables)
            }
            N::Expression(SpecExpression::Value(value)) => {
                collect_program_value_bitvector_variables(value, variables);
            }
            N::Expression(SpecExpression::ProgramExpression(expression)) => {
                collect_program_expression_bitvector_variables(expression, variables);
            }
            N::Integer(SpecIntegerExpression::Term(term)) => {
                collect_integer_variables(term, variables);
            }
            N::Proposition(proposition) => {
                if let Some((variable, body)) = proposition.quantifier() {
                    collect_spec_bitvector_variables(N::Proposition(body), variables);
                    variables.remove(&variable);
                    return Visit::Skip;
                }
            }
            _ => {}
        }
        Visit::Descend
    });
}

pub(in crate::kernel) fn collect_spec_expression_bitvector_variables(
    expression: &SpecExpression,
    variables: &mut BTreeSet<Variable>,
) {
    collect_spec_bitvector_variables(SpecNode::Expression(expression), variables);
}

pub(in crate::kernel) fn collect_spec_proposition_bitvector_variables(
    proposition: &SpecProposition,
    variables: &mut BTreeSet<Variable>,
) {
    collect_spec_bitvector_variables(SpecNode::Proposition(proposition), variables);
}

pub(crate) fn collect_spec_integer_variables(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
) {
    collect_spec_bitvector_variables(SpecNode::Integer(expression), variables);
}

/// Collect every variable identity reachable from a specification-side
/// Integer expression, including identities introduced by Integer and C
/// range-fold binders.
///
/// [`collect_spec_integer_variables`] is intentionally a free-variable
/// collector: premise indexing must not connect a fact outside a binder to a
/// variable that is local to that binder.  Fresh lowering has the opposite
/// requirement.  A newly allocated binder must be fresh from all identities
/// already present in a captured value, including bound identities and
/// mathematical Integers nested in machine payloads.  Keep that distinction
/// here, next to the term-level collectors, rather than duplicating a partial
/// specification walk in the surface elaborator.
pub(crate) fn collect_spec_integer_bound_variables(
    expression: &SpecIntegerExpression,
    variables: &mut BTreeSet<Variable>,
) {
    collect_spec_integer_variables(expression, variables);
    let mut integer_seen = SeenTerms::default();
    collect_spec_bound_identities(SpecNode::Integer(expression), variables, &mut integer_seen);
}

fn collect_integer_bound_identities(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::Machine(value) => {
            collect_machine_integer_variables(value, variables);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_pure_argument_bound_identities(argument, variables, integer_seen);
            }
        }
        IntegerTerm::Negate(value) => {
            collect_shared_integer_bound_identities(value, variables, integer_seen);
        }
        crate::kernel::binary_integer_term!(left, right) => {
            collect_shared_integer_bound_identities(left, variables, integer_seen);
            collect_shared_integer_bound_identities(right, variables, integer_seen);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_integer_variables(condition, variables, &mut SeenTerms::default());
            collect_shared_integer_bound_identities(then_term, variables, integer_seen);
            collect_shared_integer_bound_identities(else_term, variables, integer_seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_term_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_identities(binding, variables, integer_seen);
                }
                collect_shared_integer_bound_identities(&arm.body, variables, integer_seen);
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            variables.insert(*accumulator);
            variables.insert(*item);
            match index {
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    collect_machine_integer_variables(start.machine_operand(), variables);
                    collect_machine_integer_variables(end.machine_operand(), variables);
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_bound_identities(start, variables, integer_seen);
                    collect_shared_integer_bound_identities(end, variables, integer_seen);
                }
            }
            collect_shared_integer_bound_identities(initial, variables, integer_seen);
            collect_shared_integer_bound_identities(body, variables, integer_seen);
        }
    }
}

fn collect_shared_integer_bound_identities(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if integer_seen.insert(term.id()) {
        collect_integer_bound_identities(term.as_ref(), variables, integer_seen);
    }
}

fn collect_pure_argument_bound_identities(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match argument {
        PureFunctionArgument::SharedMachine(value) => {
            collect_machine_integer_variables(value, variables);
        }
        PureFunctionArgument::Value(value) => {
            collect_program_value_bound_identities(value, variables, integer_seen);
        }
        PureFunctionArgument::Integer(value) => {
            collect_shared_integer_bound_identities(value, variables, integer_seen);
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_algebraic_term_bound_identities(value, variables, integer_seen);
        }
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_program_value_bound_identities(pointer, variables, integer_seen);
        }
    }
}

fn collect_algebraic_term_bound_identities(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match &term.node {
        AlgebraicTermNode::Variable(variable) => {
            variables.insert(*variable);
        }
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_bound_identities(field, variables, integer_seen);
            }
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_algebraic_value_bound_identities(
                &load_carrier(memory.shared_memory(), pointer),
                variables,
                integer_seen,
            );
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_algebraic_value_bound_identities(
                &condition_carrier(condition),
                variables,
                integer_seen,
            );
            collect_algebraic_term_bound_identities(then_term, variables, integer_seen);
            collect_algebraic_term_bound_identities(else_term, variables, integer_seen);
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_term_bound_identities(scrutinee, variables, integer_seen);
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_bound_identities(binding, variables, integer_seen);
                }
                collect_algebraic_term_bound_identities(&arm.body, variables, integer_seen);
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_pure_argument_bound_identities(argument, variables, integer_seen);
            }
        }
    }
}

fn collect_algebraic_value_bound_identities(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match value {
        AlgebraicValue::Program(value) => {
            collect_program_value_bound_identities(value, variables, integer_seen);
        }
        AlgebraicValue::Integer(value) => {
            collect_integer_bound_identities(value, variables, integer_seen);
        }
        AlgebraicValue::Algebraic(value) => {
            collect_algebraic_term_bound_identities(value, variables, integer_seen);
        }
    }
}

fn collect_program_value_bound_identities(
    value: &ProgramValue,
    variables: &mut BTreeSet<Variable>,
    _integer_seen: &mut SeenTerms,
) {
    match value {
        ProgramValue::PointerInteger(record) => {
            collect_program_value_bound_identities(&record.numeric, variables, _integer_seen);
            collect_program_value_bound_identities(
                &ProgramValue::Pointer(*record.pointer.clone()),
                variables,
                _integer_seen,
            );
        }
        ProgramValue::Parameter(term) => {
            collect_algebraic_term_bound_identities(term, variables, _integer_seen)
        }
        ProgramValue::Void => {}
        ProgramValue::Pointer(pointer) => {
            for address in pointer.pointers() {
                if let AddressBase::PureFunctionApplication(application) = &address.base
                    && _integer_seen.pointers.insert(application.id())
                {
                    for argument in application.arguments() {
                        collect_pure_argument_bound_identities(argument, variables, _integer_seen);
                    }
                }
            }
        }
        ProgramValue::Int8(bits) => {
            collect_bitvector_integer_variables(bits, variables);
        }
        ProgramValue::Bool(bits)
        | ProgramValue::Int16(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt32(bits)
        | ProgramValue::Int64(bits)
        | ProgramValue::UInt64(bits)
        | ProgramValue::Int128(bits)
        | ProgramValue::UInt128(bits)
        | ProgramValue::Float32(bits)
        | ProgramValue::Float64(bits) => {
            collect_bitvector_integer_variables(bits, variables);
        }
    }
}

fn collect_program_expression_bound_identities(
    expression: &ProgramExpression,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    match expression {
        ProgramExpression::Value(value) => {
            collect_program_value_bound_identities(value, variables, integer_seen);
        }
        ProgramExpression::Variable(_)
        | ProgramExpression::StringLiteral(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Cast { expression, .. }
        | ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        }
        | ProgramExpression::AddressOf(expression)
        | ProgramExpression::CheckedObjectAddress(expression)
        | ProgramExpression::Not(expression)
        | ProgramExpression::Load(expression)
        | ProgramExpression::TypedLoad {
            pointer: expression,
            ..
        }
        | ProgramExpression::BitwiseNot(expression) => {
            collect_program_expression_bound_identities(expression, variables, integer_seen);
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_program_expression_bound_identities(field, variables, integer_seen);
            }
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_program_expression_bound_identities(condition, variables, integer_seen);
            collect_program_expression_bound_identities(then_branch, variables, integer_seen);
            collect_program_expression_bound_identities(else_branch, variables, integer_seen);
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            collect_program_expression_bound_identities(pointer, variables, integer_seen);
        }
        crate::kernel::binary_c_expression!(left, right) => {
            collect_program_expression_bound_identities(left, variables, integer_seen);
            collect_program_expression_bound_identities(right, variables, integer_seen);
        }
    }
}

/// Collects every variable identity in a specification subtree, bound or
/// free, for freshness. Quantifier, Integer fold and Integer match-arm
/// binders count; a specification memory is a captured execution state,
/// not lexical input, so only the explicit pointer and expression payloads
/// beside it are visited.
fn collect_spec_bound_identities(
    root: SpecNode<'_>,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    walk_spec::<()>(root, WalkBudget::Unmetered, |node| {
        use SpecNode as N;
        match node {
            N::Resource(SpecResource::Value(resource)) => {
                collect_resource_bitvector_variables(resource, variables)
            }
            N::Expression(SpecExpression::Value(value)) => {
                collect_program_value_bound_identities(value, variables, integer_seen);
            }
            N::Expression(SpecExpression::ProgramExpression(expression)) => {
                collect_program_expression_bound_identities(expression, variables, integer_seen);
            }
            N::Expression(SpecExpression::ResourceField { projection, .. })
            | N::Integer(SpecIntegerExpression::ResourceField(projection)) => {
                variables.insert(projection.identity);
            }
            N::Integer(SpecIntegerExpression::Term(term)) => {
                collect_integer_bound_identities(term, variables, integer_seen);
            }
            N::Integer(SpecIntegerExpression::AlgebraicMatch { arms, .. }) => {
                variables.extend(
                    arms.iter()
                        .flat_map(|arm| arm.binding_variables.iter().flatten().copied()),
                );
            }
            N::Integer(SpecIntegerExpression::RangeFold {
                accumulator, item, ..
            }) => variables.extend([*accumulator, *item]),
            N::Algebraic(SpecAlgebraicExpression {
                node: SpecAlgebraicExpressionNode::Variable(variable),
                ..
            }) => {
                variables.insert(*variable);
            }
            N::Proposition(proposition) => {
                if let Some((variable, _)) = proposition.quantifier() {
                    variables.insert(variable);
                }
            }
            _ => {}
        }
        Visit::Descend
    });
}

#[cfg(test)]
pub(crate) fn collect_spec_algebraic_expression_bitvector_variables(
    expression: &SpecAlgebraicExpression,
    variables: &mut BTreeSet<Variable>,
) {
    collect_spec_bitvector_variables(SpecNode::Algebraic(expression), variables);
}

pub(in crate::kernel) fn collect_loop_effect_bitvector_variables(
    effect: &LoopEffect,
    variables: &mut BTreeSet<Variable>,
) {
    match effect {
        LoopEffect::Mutable(segments) => {
            for segment in segments {
                collect_program_expression_bitvector_variables(&segment.base, variables);
                collect_program_expression_bitvector_variables(&segment.start, variables);
                collect_program_expression_bitvector_variables(&segment.end, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_program_expression_outcome_bitvector_variables(
    outcome: &ExpressionOutcome<crate::kernel::StoredProgramValue>,
    variables: &mut BTreeSet<Variable>,
) {
    if let ExpressionOutcome::Value(value) = outcome {
        collect_expression_value_bitvector_variables(value.value(), variables);
    }
}

pub(in crate::kernel) fn collect_execution_statement_outcome_bitvector_variables(
    outcome: &StatementOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        StatementOutcome::Normal(state) => {
            collect_execution_state_bitvector_variables(state, variables)
        }
        StatementOutcome::LoopTestFalse(state)
        | StatementOutcome::Break(state)
        | StatementOutcome::Continue(state)
        | StatementOutcome::Jump { state, .. } => {
            collect_execution_state_bitvector_variables(state, variables)
        }
        StatementOutcome::Return { value, state } | StatementOutcome::Throw { value, state } => {
            collect_expression_value_bitvector_variables(value, variables);
            collect_execution_state_bitvector_variables(state, variables);
        }
        StatementOutcome::VerificationDiverges
        | StatementOutcome::UndefinedBehavior(_)
        | StatementOutcome::RuntimeError(_) => {}
    }
}

pub(in crate::kernel) fn collect_program_function_outcome_bitvector_variables(
    outcome: &FunctionOutcome,
    variables: &mut BTreeSet<Variable>,
) {
    match outcome {
        FunctionOutcome::Return { value, state } | FunctionOutcome::Throw { value, state } => {
            collect_expression_value_bitvector_variables(value, variables);
            collect_execution_state_bitvector_variables(state, variables);
        }
        FunctionOutcome::VerificationDiverges
        | FunctionOutcome::UndefinedBehavior(_)
        | FunctionOutcome::RuntimeError(_) => {}
    }
}

pub(in crate::kernel) fn collect_execution_state_bitvector_variables(
    state: &ExecutionState,
    variables: &mut BTreeSet<Variable>,
) {
    if let Some(destination) = &state.aggregate_destination {
        collect_pointer_bitvector_variables(&destination.pointer, variables);
    }
    for binding in state.locals.bindings.values() {
        match binding {
            LocalBinding::Object { value, .. } => {
                collect_expression_value_bitvector_variables(value, variables)
            }
            LocalBinding::UninitializedObject { .. } => {}
            LocalBinding::GlobalObject { .. } => {}
            LocalBinding::ArrayObject { .. } => {}
            LocalBinding::AggregateObject { .. } => {}
        }
    }
    collect_memory_bitvector_variables(&state.memory, variables);
    collect_resource_context_bitvector_variables(&state.resources, variables);
    collect_resource_context_bitvector_variables(&state.instance_field_scope, variables);
}

pub(in crate::kernel) fn collect_resource_context_bitvector_variables(
    resources: &ResourceContext,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in resources.facts() {
        collect_resource_fact_bitvector_variables(resource, variables);
    }
}

#[cfg(test)]
thread_local! {
    /// Resource facts collected, for the composition ceiling regression.
    pub(in crate::kernel) static COLLECTED_RESOURCE_FACTS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

pub(in crate::kernel) fn collect_resource_fact_bitvector_variables(
    resource: &ResourceFact,
    variables: &mut BTreeSet<Variable>,
) {
    #[cfg(test)]
    COLLECTED_RESOURCE_FACTS.with(|count| count.set(count.get() + 1));
    collect_resource_bitvector_variables(resource.resource(), variables);
}

pub(in crate::kernel) fn collect_resource_bitvector_variables(
    resource: &Resource,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        Resource::Star(pair) => {
            collect_resource_bitvector_variables(&pair.0, variables);
            collect_resource_bitvector_variables(&pair.1, variables);
        }
        Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp => {}
        Resource::PopulationAuthority(description) => {
            description.visit_values(|value| {
                collect_algebraic_value_bitvector_variables(value, variables)
            });
        }
        Resource::MutexUse(identity) => {
            if let Some(p) = &identity.protected {
                p.visit_values(|v| collect_algebraic_value_bitvector_variables(v, variables));
            }
            if identity.binding.is_none() {
                collect_pointer_bitvector_variables(&identity.mutex, variables);
            }
        }
        Resource::ConditionalMutexGuard(carrier) => {
            collect_condition_bitvector_variables(carrier.condition(), variables)
        }
        Resource::MutexGuard(identity) | Resource::MutexLive(identity) => {
            if identity.epoch.is_none() {
                let pointer = &identity.mutex;
                collect_pointer_bitvector_variables(pointer, variables);
            }
        }
        Resource::Publication(right) => {
            right
                .payload
                .visit_values(|v| collect_algebraic_value_bitvector_variables(v, variables));
            collect_pointer_bitvector_variables(&right.flag, variables);
            if let Some(value) = &right.observed {
                collect_expression_value_bitvector_variables(value.value(), variables);
            }
        }
        Resource::Instance(instance) => {
            for value in instance.arguments.iter() {
                collect_algebraic_value_bitvector_variables(value, variables);
            }
            for index in 0..instance.fields.len() {
                if let Some(value) = instance.fields.retained_program(index) {
                    collect_expression_value_bitvector_variables(value, variables);
                } else {
                    collect_algebraic_value_bitvector_variables(
                        instance.fields.get(index).expect("field index"),
                        variables,
                    );
                }
            }
            crate::kernel::ResourceReference::visit_captured_values(
                instance.resource_arguments(),
                |value| {
                    collect_algebraic_value_bitvector_variables(value, variables);
                },
            );
        }
        Resource::Memory(range) => collect_memory_range_bitvector_variables(range, variables),
        Resource::Iterated(iterated) => {
            for pointer in iterated.pointers() {
                collect_pointer_bitvector_variables(pointer, variables);
            }
            for term in iterated.terms() {
                collect_bitvector_variables(term, variables);
            }
        }
        Resource::Composite { arguments, .. } | Resource::Token { arguments, .. } => {
            for argument in arguments.iter() {
                collect_algebraic_value_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_program_function_bitvector_variables(
    function: &ProgramFunction,
    variables: &mut BTreeSet<Variable>,
) {
    collect_program_function_contract_interface_bitvector_variables(
        function.contract_interface(),
        variables,
    );
    collect_execution_statement_bitvector_variables(function.body(), variables);
}

/// Collects variables from the body-independent contract interface only.
/// Named callback application uses this collector so unrelated template
/// statements, globals, and storage cannot affect fresh identities or
/// callback behavior.
pub(in crate::kernel) fn collect_program_function_contract_interface_bitvector_variables(
    interface: &FunctionContractInterface,
    variables: &mut BTreeSet<Variable>,
) {
    for resource in interface
        .proof_parameters()
        .iter()
        .chain(interface.resource_requires())
        .chain(interface.resource_ensures())
        .chain(interface.resource_constructors())
    {
        collect_resource_spec_bitvector_variables(resource, variables);
    }
    for proposition in interface
        .contract_requires()
        .iter()
        .chain(interface.contract_ensures())
        .chain(interface.exceptional_ensures())
    {
        collect_spec_proposition_bitvector_variables(proposition, variables);
    }
    for segment in interface.contract_mutable() {
        collect_program_expression_bitvector_variables(&segment.base, variables);
        collect_program_expression_bitvector_variables(&segment.start, variables);
        collect_program_expression_bitvector_variables(&segment.end, variables);
        if let Some(guard) = segment.guard() {
            collect_spec_proposition_bitvector_variables(guard, variables);
        }
    }
    for measure in interface.recursion_measure().unwrap_or_default() {
        collect_ranking_component_variables(measure, variables);
    }
}

pub(in crate::kernel) fn collect_resource_spec_bitvector_variables(
    resource: &ResourceSpec,
    variables: &mut BTreeSet<Variable>,
) {
    match resource.term() {
        ResourceTerm::Instance { resource, .. } => {
            collect_resource_term_bitvector_variables(resource, variables)
        }
        ResourceTerm::PopulationAuthority { protected, .. } => {
            collect_resource_spec_bitvector_variables(&protected.resource, variables)
        }
        ResourceTerm::MutexGuard { mutex, .. } | ResourceTerm::MutexLive { mutex, .. } => {
            collect_program_expression_bitvector_variables(mutex, variables)
        }
        ResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_program_expression_bitvector_variables(mutex, variables);
            if let Some(p) = protected {
                collect_resource_spec_bitvector_variables(&p.resource, variables);
            }
        }
        ResourceTerm::Publication { flag, payload, .. } => {
            collect_program_expression_bitvector_variables(flag, variables);
            collect_resource_spec_bitvector_variables(&payload.resource, variables);
        }
        ResourceTerm::Memory(segment) => {
            collect_program_expression_bitvector_variables(&segment.base, variables);
            collect_program_expression_bitvector_variables(&segment.start, variables);
            collect_program_expression_bitvector_variables(&segment.end, variables);
            if let Some(guard) = segment.guard() {
                collect_spec_proposition_bitvector_variables(guard, variables);
            }
        }
        ResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_program_expression_bitvector_variables(expression, variables);
            }
        }
        ResourceTerm::Composite { arguments, .. } | ResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_program_expression_bitvector_variables(argument, variables);
            }
        }
    }
    if let ResourceQuantity::Count(quantity) = resource.quantity() {
        collect_program_expression_bitvector_variables(quantity, variables);
    }
}

fn collect_resource_term_bitvector_variables(
    resource: &ResourceTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match resource {
        ResourceTerm::Instance { resource, .. } => {
            collect_resource_term_bitvector_variables(resource, variables)
        }
        ResourceTerm::PopulationAuthority { protected, .. } => {
            collect_resource_spec_bitvector_variables(&protected.resource, variables)
        }
        ResourceTerm::MutexGuard { mutex, .. } | ResourceTerm::MutexLive { mutex, .. } => {
            collect_program_expression_bitvector_variables(mutex, variables)
        }
        ResourceTerm::MutexUse {
            mutex, protected, ..
        } => {
            collect_program_expression_bitvector_variables(mutex, variables);
            if let Some(p) = protected {
                collect_resource_spec_bitvector_variables(&p.resource, variables);
            }
        }
        ResourceTerm::Publication { flag, payload, .. } => {
            collect_program_expression_bitvector_variables(flag, variables);
            collect_resource_spec_bitvector_variables(&payload.resource, variables);
        }
        ResourceTerm::Memory(segment) => {
            collect_program_expression_bitvector_variables(&segment.base, variables);
            collect_program_expression_bitvector_variables(&segment.start, variables);
            collect_program_expression_bitvector_variables(&segment.end, variables);
            if let Some(guard) = segment.guard() {
                collect_spec_proposition_bitvector_variables(guard, variables);
            }
        }
        ResourceTerm::Iterated(spec) => {
            for expression in spec.expressions() {
                collect_program_expression_bitvector_variables(expression, variables);
            }
        }
        ResourceTerm::Composite { arguments, .. } | ResourceTerm::Token { arguments, .. } => {
            for argument in arguments {
                collect_program_expression_bitvector_variables(argument, variables);
            }
        }
    }
}

pub(in crate::kernel) fn collect_program_function_specification_bitvector_variables(
    specification: &FunctionSpecification,
    variables: &mut BTreeSet<Variable>,
) {
    collect_execution_state_bitvector_variables(specification.state(), variables);
    for argument in specification.arguments() {
        collect_program_expression_bitvector_variables(argument, variables);
    }
    for requirement in specification.requires() {
        collect_proposition_bitvector_variables(requirement, variables);
    }
    collect_program_function_outcome_bitvector_variables(specification.outcome(), variables);
}

pub(in crate::kernel) fn collect_assumption_variables(
    assumptions: &PureFactContext,
    variables: &mut BTreeSet<Variable>,
) {
    for proposition in assumptions.pure_facts() {
        collect_proposition_bitvector_variables(&proposition, variables);
    }
}

#[cfg(test)]
pub(in crate::kernel) fn collect_execution_environment_variables(
    environment: &ExecutionEnvironment,
    variables: &mut BTreeSet<Variable>,
) {
    variables.extend(
        execution_environment_variable_index(environment)
            .iter()
            .copied(),
    );
}

/// The variables `environment` reserves. Its own parts and each verified
/// loop rule are indexed separately, each once for every clone sharing it:
/// a proof's `loop` tactic adds one rule to an environment holding all the
/// earlier ones, and must not collect those again.
pub(in crate::kernel) fn execution_environment_variable_index(
    environment: &ExecutionEnvironment,
) -> crate::kernel::ReservedVariableSets {
    let mut sets =
        crate::kernel::ReservedVariableSets::from(environment.variable_index.get_or_init(|| {
            let mut variables = BTreeSet::new();
            collect_execution_environment_variables_uncached(environment, &mut variables);
            variables
        }));
    if let Some(rules) = environment.verified_loop_rules.reserved_variables() {
        sets.push_lazy(rules);
    }
    sets
}

/// At least the greatest execution-range variable a verified loop rule
/// reserves, without collecting its prerequisite context: that context
/// keeps such a bound as its facts are filed, and only the rule's
/// loop-local parts are read here, once per rule.
pub(in crate::kernel) fn verified_loop_rule_execution_bound(
    rule: &crate::kernel::VerifiedLoopRule,
) -> Option<Variable> {
    rule.variable_index.execution_bound(|| {
        let (local, _) = execution_variable_ceiling(None, |variables| {
            collect_verified_loop_rule_local_variables(rule, variables);
        });
        local.max(rule.required_assumptions.execution_variable_ceiling())
    })
}

/// Every variable a verified loop rule reserves, collected once and shared
/// by the rule's clones. Its prerequisite context is the whole path context
/// at its loop, so this is linear in everything before the loop.
pub(in crate::kernel) fn verified_loop_rule_variables(
    rule: &crate::kernel::VerifiedLoopRule,
) -> std::sync::Arc<BTreeSet<Variable>> {
    rule.variable_index.get_or_init(|| {
        let mut variables = BTreeSet::new();
        collect_verified_loop_rule_variables(rule, &mut variables);
        variables
    })
}

/// The variables of a rule's prerequisite context: its facts' free and
/// bound variables. Execution-range binders are never minted (every binder
/// producer has its own range), so the context's execution ceiling bounds
/// the execution-range variables collected here.
pub(in crate::kernel) fn collect_assumption_reserved_variables(
    assumptions: &PureFactContext,
    variables: &mut BTreeSet<Variable>,
) {
    collect_assumption_variables(assumptions, variables);
    for fact in assumptions.pure_facts() {
        collect_proposition_bound_variables(&fact, variables);
    }
}

fn collect_execution_environment_variables_uncached(
    environment: &ExecutionEnvironment,
    variables: &mut BTreeSet<Variable>,
) {
    for function in environment.functions.values() {
        collect_program_function_bitvector_variables(function, variables);
        collect_program_function_bound_variables(function, variables);
    }
    for contract in environment.function_contracts.values() {
        collect_program_function_contract_interface_bitvector_variables(
            contract.interface(),
            variables,
        );
        collect_program_function_contract_interface_bound_variables(
            contract.interface(),
            variables,
        );
    }
    for rule in environment.verified_function_rules.values() {
        collect_program_function_bitvector_variables(&rule.function, variables);
        collect_program_function_bound_variables(&rule.function, variables);
    }
    // The anchor holds the certified function's measure read at its entry.
    // Its variables are named by later call steps, so a fresh identity must
    // not be handed out on top of one, exactly as for a loop head's measure.
    if let Some(anchor) = environment.recursion_anchor() {
        for measure in anchor.measure() {
            match measure {
                RankingMeasureValue::Machine(term)
                | RankingMeasureValue::Unsigned32(term)
                | RankingMeasureValue::Unsigned64(term)
                | RankingMeasureValue::Signed64(term) => {
                    collect_bitvector_variables(term, variables)
                }
                // An Integer measure's reserved names are the C carriers it
                // reads plus its own Integer binders; both are named by later
                // call steps.
                RankingMeasureValue::Integer(term) => {
                    collect_integer_capture_bitvector_variables(term, variables);
                    collect_integer_variables(term, variables);
                }
            }
        }
        for component in anchor.components() {
            collect_ranking_component_variables(component, variables);
        }
        // A structural anchor holds the entry instance whose model later call
        // steps compare against, so its names are reserved like a measure's.
        if let Some(entry) = anchor.structural_entry() {
            variables.insert(entry.identity);
            for value in entry.arguments.iter() {
                collect_algebraic_value_bitvector_variables(value, variables);
            }
            for index in 0..entry.fields.len() {
                if let Some(value) = entry.fields.retained_program(index) {
                    collect_expression_value_bitvector_variables(value, variables);
                } else {
                    collect_algebraic_value_bitvector_variables(
                        entry.fields.get(index).expect("field index"),
                        variables,
                    );
                }
            }
        }
        for obligation in anchor.entry_obligations() {
            collect_proposition_bitvector_variables(obligation.proposition(), variables);
            collect_proposition_bound_variables(obligation.proposition(), variables);
        }
    }
}

fn collect_verified_loop_rule_variables(
    rule: &crate::kernel::VerifiedLoopRule,
    variables: &mut BTreeSet<Variable>,
) {
    collect_verified_loop_rule_local_variables(rule, variables);
    collect_assumption_reserved_variables(&rule.required_assumptions, variables);
}

/// A rule's variables other than its prerequisite context's: its entry
/// state, loop statement and certified paths.
fn collect_verified_loop_rule_local_variables(
    rule: &crate::kernel::VerifiedLoopRule,
    variables: &mut BTreeSet<Variable>,
) {
    collect_execution_state_bitvector_variables(&rule.symbolic_entry_state, variables);
    collect_execution_state_bound_variables(&rule.symbolic_entry_state, variables);
    collect_execution_statement_bitvector_variables(&rule.loop_statement, variables);
    collect_execution_statement_bound_variables(&rule.loop_statement, variables);
    for path in &rule.paths {
        collect_execution_statement_outcome_bitvector_variables(&path.outcome, variables);
        collect_statement_outcome_bound_variables(&path.outcome, variables);
        for fact in &path.facts {
            collect_proposition_bitvector_variables(fact.proposition(), variables);
            collect_proposition_bound_variables(fact.proposition(), variables);
        }
        for obligation in &path.obligations {
            collect_proposition_bitvector_variables(obligation.proposition(), variables);
            collect_proposition_bound_variables(obligation.proposition(), variables);
        }
    }
}

pub(in crate::kernel) fn collect_memory_range_bitvector_variables(
    range: &MemoryRange,
    variables: &mut BTreeSet<Variable>,
) {
    for fact in range.formation_coverage.iter() {
        collect_proposition_bitvector_variables(fact, variables);
    }
    collect_pointer_bitvector_variables(&range.base, variables);
    collect_bitvector_variables(range.bound_terms().0, variables);
    collect_bitvector_variables(range.bound_terms().1, variables);
}

pub(crate) fn resource_context_has_read(
    resources: &ResourceContext,
    pointer: &Address,
    byte_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    // Resource-backed reads are loadability checks too: a view retained
    // across an opaque effect may name its bounds with load atoms from the
    // pre-effect state, while the expression being loaded names the same
    // cells at the current state. Keep the state-DAG bridge scoped to
    // this resource-backed access query, just as `proves_memory_loadable`
    // does for proposition-backed loadability facts.
    crate::kernel::api::with_extended_dag_bridging(|| {
        resources.permits_memory_read(pointer, byte_width, assumptions)
    })
}

/// Charge one collector node and report whether the checked fold analysis has
/// already exhausted its deterministic budget.  The instrumentation scope is
/// inactive for legacy callers, so those callers retain their existing work
/// accounting while the checked constructors can stop before descending into
/// another payload.
#[inline]
fn checked_collection_checkpoint() -> bool {
    #[cfg(test)]
    crate::instrumentation::record_checked_collection_attempt();
    crate::instrumentation::record_deterministic_work(1);
    crate::instrumentation::checked_collection_exhausted()
}

thread_local! {
    // Condition-index insertion reads syntax, never state contents. A
    // state-dependent fact is indexed lazily by the ordinary collector.
    static DEFER_CONDITION_STATES: std::cell::Cell<Option<bool>> = const { std::cell::Cell::new(None) };
}

struct ConditionStateDeferral(Option<bool>);

impl Drop for ConditionStateDeferral {
    fn drop(&mut self) {
        DEFER_CONDITION_STATES.with(|state| state.set(self.0));
    }
}

fn defer_condition_state() -> bool {
    DEFER_CONDITION_STATES.with(|state| {
        if state.get().is_some() {
            state.set(Some(true));
            true
        } else {
            false
        }
    })
}

thread_local! {
    static COORDINATE_VARIABLES: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Equality-source dependencies include byte-offset variables as well as
/// machine-value variables. Preserve the ordinary state deferral policy.
pub(in crate::kernel) fn collect_condition_coordinate_index_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) -> bool {
    struct Scope(bool);
    impl Drop for Scope {
        fn drop(&mut self) {
            COORDINATE_VARIABLES.with(|flag| flag.set(self.0));
        }
    }
    let _scope = Scope(COORDINATE_VARIABLES.with(|flag| flag.replace(true)));
    collect_condition_index_variables(condition, variables)
}

/// Collect the ordinary condition variables, stopping at each state.
/// Returns whether a state was encountered. If so, the caller must defer
/// the whole fact to the complete collector to preserve its connections.
pub(in crate::kernel) fn collect_condition_index_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) -> bool {
    let prior = DEFER_CONDITION_STATES.with(|state| state.replace(Some(false)));
    let _scope = ConditionStateDeferral(prior);
    collect_condition_bitvector_variables(condition, variables);
    DEFER_CONDITION_STATES.with(|state| state.get() == Some(true))
}

pub(crate) fn collect_condition_bitvector_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
) {
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_bitvector_variables(pointer, variables);
            }
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_algebraic_term_bitvector_variables(left, variables);
            collect_algebraic_term_bitvector_variables(right, variables);
        }
        ConditionTerm::Constant(_) => {}
        ConditionTerm::Variable(variable) => {
            if collecting_connection_variables() {
                variables.insert(*variable);
            }
        }
        crate::kernel::binary_bitvector_condition!(left, right) => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition
                .for_each_bitvector_term(|term| collect_bitvector_variables(term, variables));
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
        ConditionTerm::AddressEqual(left, right) => {
            collect_pointer_bitvector_variables(left, variables);
            collect_pointer_bitvector_variables(right, variables);
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_integer_variables(left, variables);
            collect_integer_variables(right, variables);
        }
        ConditionTerm::BoolApplication(application) => {
            collect_application_connection_variables(application.arguments(), variables);
        }
        ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => {
            for child in condition.bool_children() {
                collect_condition_bitvector_variables(child, variables);
            }
        }
        ConditionTerm::BoolLoad(memory, pointer) => {
            collect_shared_memory_bitvector_variables(memory.shared_memory(), variables);
            collect_pointer_bitvector_variables(pointer, variables);
            collect_stored_load_connection_variables(memory.shared_memory(), pointer, variables);
        }
    }
}

/// An application's arguments are not free bitvector variables of the
/// term, but a fact about one of them is related to it.
fn collect_application_connection_variables(
    arguments: &[PureFunctionArgument],
    variables: &mut BTreeSet<Variable>,
) {
    if !collecting_connection_variables() {
        return;
    }
    for argument in arguments {
        match argument {
            PureFunctionArgument::SharedMachine(value) => {
                collect_machine_bitvector_variables(value, variables)
            }
            PureFunctionArgument::Value(value) => {
                collect_program_value_bitvector_variables(value, variables)
            }
            PureFunctionArgument::Algebraic(value) => {
                collect_algebraic_term_bitvector_variables(value, variables)
            }
            PureFunctionArgument::Integer(value) => collect_integer_variables(value, variables),
            PureFunctionArgument::ArrayRef { pointer, .. } => {
                collect_program_value_bitvector_variables(pointer, variables)
            }
        }
    }
}

pub(crate) fn collect_integer_variables(term: &IntegerTerm, variables: &mut BTreeSet<Variable>) {
    let mut seen = SeenTerms::default();
    collect_integer_variables_seen(term, variables, &mut seen);
}

/// Collect variables used as mathematical Integer binders, excluding C
/// variables embedded in `IntegerTerm::Machine` nodes.  Integer-to-machine
/// payloads nested inside those C terms remain visible because they carry a
/// mathematical Integer expression of their own.
pub(crate) fn collect_integer_carrier_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = SeenTerms::default();
    collect_integer_carrier_variables_seen(term, variables, &mut seen);
}

fn collect_integer_carrier_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Machine(value) => visit_machine_carrier_leaves(value, |leaf| {
            collect_operand_integer_variables_seen(leaf, variables, seen)
        }),
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                if let PureFunctionArgument::Integer(value) = argument {
                    collect_shared_integer_carrier_variables_seen(value, variables, seen);
                }
            }
        }
        IntegerTerm::Negate(value) => {
            collect_shared_integer_carrier_variables_seen(value, variables, seen)
        }
        crate::kernel::binary_integer_term!(left, right) => {
            collect_shared_integer_carrier_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(right, variables, seen);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_integer_variables(condition, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(then_term, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(else_term, variables, seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_algebraic_value_integer_variables(binding, variables, seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_shared_integer_carrier_variables_seen(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_carrier_variables_seen(start, variables, seen);
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_shared_integer_carrier_variables_seen(end, variables, seen);
                }
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    for endpoint in [start, end] {
                        visit_machine_carrier_leaves(endpoint.machine_operand(), |leaf| {
                            collect_operand_integer_variables_seen(leaf, variables, seen);
                        });
                        if crate::instrumentation::checked_collection_exhausted() {
                            return;
                        }
                    }
                }
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(initial, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_carrier_variables_seen(body, variables, seen);
            variables.insert(*accumulator);
            if matches!(index, IntegerRangeFoldIndex::Integer { .. }) {
                variables.insert(*item);
            }
        }
    }
}

fn collect_shared_integer_carrier_variables_seen(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    if seen.insert(term.id()) {
        collect_integer_carrier_variables_seen(term.as_ref(), variables, seen);
    }
}

/// Collect mathematical Integer variables nested in a machine term.  SymbolicMemory
/// states are intentionally opaque here: only the address payload of a
/// load can carry a variable relevant to a lexical substitution, and that
/// payload is a machine term with no Integer carrier.
pub(crate) fn collect_bitvector_integer_variables(
    term: &MachineTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = SeenTerms::default();
    collect_bitvector_integer_variables_seen(term, variables, &mut seen);
}

fn collect_bitvector_integer_variables_seen(
    term: &MachineTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        MachineTerm::ThreadHandle(_) => {}
        MachineTerm::Constant { .. } | MachineTerm::Variable(_) => {}
        MachineTerm::MemoryLoad(_, pointer, _) | MachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_integer_variables(pointer, variables, seen)
        }
        MachineTerm::IntegerToMachine { value, .. } => {
            collect_shared_integer_variables_seen(value, variables, seen);
        }
        crate::kernel::binary_machine_term!(left, right) => {
            collect_bitvector_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(right, variables, seen);
        }
        crate::kernel::unary_machine_term!(value) => {
            collect_bitvector_integer_variables_seen(value, variables, seen)
        }
        MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            collect_bitvector_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(right, variables, seen);
        }
        MachineTerm::BoolCast { value, .. } => {
            collect_condition_integer_variables(value, variables, seen)
        }
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_integer_variables(condition, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(then_term, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(else_term, variables, seen);
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_integer_variables_seen(start, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(end, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(initial, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_integer_variables_seen(body, variables, seen);
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_integer_variables_seen(argument, variables, seen);
            }
        }
        MachineTerm::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_pure_argument_integer_variables(argument, variables, seen);
            }
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_algebraic_value_integer_variables(binding, variables, seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_integer_variables_seen(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
    }
}

fn collect_pointer_integer_variables(
    pointer: &Address,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    if let AddressBase::PureFunctionApplication(application) = &pointer.base
        && seen.pointers.insert(application.id())
    {
        for argument in application.arguments() {
            collect_pure_argument_integer_variables(argument, variables, seen);
        }
    }
    collect_pointer_offset_integer_variables(&pointer.offset, variables, seen);
}

fn collect_pointer_offset_integer_variables(
    offset: &AddressOffset,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match offset {
        AddressOffset::Constant(_) | AddressOffset::Variable(_) => {}
        AddressOffset::Add(left, right) => {
            collect_pointer_offset_integer_variables(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_integer_variables(right, variables, seen);
        }
        AddressOffset::Int32Scaled { value, .. } | AddressOffset::Int64Scaled { value, .. } => {
            visit_machine_carrier_leaves(value, |leaf| {
                collect_operand_integer_variables_seen(leaf, variables, seen)
            });
        }
    }
}

fn collect_shared_integer_variables_seen(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    if seen.insert(term.id()) {
        collect_integer_free_variables_seen(term.as_ref(), variables, seen);
    }
}

fn collect_integer_free_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if retained_folds::collect_native_fold_variables(
        term,
        retained_folds::FoldVariableRead::IntegerFree,
        variables,
    ) {
        return;
    }

    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Machine(value) => visit_machine_carrier_leaves(value, |leaf| {
            collect_operand_integer_variables_seen(leaf, variables, seen)
        }),
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                match argument {
                    PureFunctionArgument::Integer(value) => {
                        collect_shared_integer_variables_seen(value, variables, seen)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_free_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::SharedMachine(value) => {
                        visit_machine_carrier_leaves(value, |leaf| {
                            collect_operand_integer_variables_seen(leaf, variables, seen);
                        });
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_program_value_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::ArrayRef { pointer, .. } => {
                        collect_program_value_integer_variables(pointer, variables, seen)
                    }
                }
            }
        }
        IntegerTerm::Negate(value) => collect_shared_integer_variables_seen(value, variables, seen),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_shared_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(right, variables, seen);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_integer_variables(condition, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(then_term, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(else_term, variables, seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_free_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                let mut body_variables = BTreeSet::new();
                collect_shared_integer_variables_seen(
                    &arm.body,
                    &mut body_variables,
                    &mut SeenTerms::default(),
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                for binding in &arm.bindings {
                    if let AlgebraicValue::Integer(value) = binding
                        && let IntegerTerm::Variable(variable) = value
                    {
                        body_variables.remove(variable);
                    }
                }
                variables.extend(body_variables);
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_variables_seen(start, variables, seen);
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_shared_integer_variables_seen(end, variables, seen);
                }
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    for endpoint in [start, end] {
                        visit_machine_carrier_leaves(endpoint.machine_operand(), |leaf| {
                            collect_operand_integer_variables_seen(leaf, variables, seen);
                        });
                        if crate::instrumentation::checked_collection_exhausted() {
                            return;
                        }
                    }
                }
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(initial, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            let mut body_variables = BTreeSet::new();
            collect_shared_integer_variables_seen(
                body,
                &mut body_variables,
                &mut SeenTerms::default(),
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            body_variables.remove(accumulator);
            if matches!(index, IntegerRangeFoldIndex::Integer { .. }) {
                body_variables.remove(item);
            }
            variables.extend(body_variables);
        }
    }
}

fn collect_algebraic_free_integer_variables(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                match field {
                    AlgebraicValue::Program(value) => {
                        collect_program_value_integer_variables(value, variables, seen)
                    }
                    AlgebraicValue::Integer(value) => {
                        collect_integer_free_variables_seen(value, variables, seen)
                    }
                    AlgebraicValue::Algebraic(value) => {
                        collect_algebraic_free_integer_variables(value, variables, seen)
                    }
                }
            }
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_algebraic_value_integer_variables(
                &load_carrier(memory.shared_memory(), pointer),
                variables,
                seen,
            );
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_algebraic_value_integer_variables(
                &condition_carrier(condition),
                variables,
                seen,
            );
            collect_algebraic_free_integer_variables(then_term, variables, seen);
            collect_algebraic_free_integer_variables(else_term, variables, seen);
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_free_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    match binding {
                        AlgebraicValue::Program(value) => {
                            collect_program_value_integer_variables(value, variables, seen)
                        }
                        AlgebraicValue::Integer(value) => {
                            collect_integer_free_variables_seen(value, variables, seen)
                        }
                        AlgebraicValue::Algebraic(value) => {
                            collect_algebraic_free_integer_variables(value, variables, seen)
                        }
                    }
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_algebraic_free_integer_variables(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                match argument {
                    PureFunctionArgument::SharedMachine(value) => {
                        visit_machine_carrier_leaves(value, |leaf| {
                            collect_operand_integer_variables_seen(leaf, variables, seen);
                        });
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_program_value_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::Integer(value) => {
                        collect_shared_integer_variables_seen(value, variables, seen)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_free_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::ArrayRef { pointer, .. } => {
                        collect_program_value_integer_variables(pointer, variables, seen)
                    }
                }
            }
        }
    }
}

/// Collect free mathematical Integer variables, preserving the Integer/C
/// carrier boundary through pure and algebraic arguments.
pub(crate) fn collect_integer_free_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut seen = SeenTerms::default();
    collect_integer_free_variables_seen(term, variables, &mut seen);
}

fn collect_condition_integer_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match condition {
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_shared_integer_variables_seen(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_variables_seen(right, variables, seen);
        }
        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_algebraic_integer_variables(left, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_algebraic_integer_variables(right, variables, seen);
        }
        _ => {}
    }
}

fn collect_pure_argument_integer_variables(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match argument {
        PureFunctionArgument::Integer(value) => {
            collect_shared_integer_variables_seen(value, variables, seen)
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_algebraic_integer_variables(value, variables, seen)
        }
        PureFunctionArgument::SharedMachine(value) => {
            visit_machine_carrier_leaves(value, |leaf| {
                collect_operand_integer_variables_seen(leaf, variables, seen);
            });
        }
        PureFunctionArgument::Value(value) => {
            collect_program_value_integer_variables(value, variables, seen)
        }
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_program_value_integer_variables(pointer, variables, seen)
        }
    }
}

fn collect_program_value_integer_variables(
    value: &ProgramValue,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        ProgramValue::PointerInteger(record) => {
            collect_program_value_integer_variables(&record.numeric, variables, seen);
            collect_program_value_integer_variables(
                &ProgramValue::Pointer(*record.pointer.clone()),
                variables,
                seen,
            );
        }
        ProgramValue::Void => {}
        ProgramValue::Int8(value) => {
            collect_bitvector_integer_variables_seen(value, variables, seen)
        }
        ProgramValue::Bool(value)
        | ProgramValue::Int16(value)
        | ProgramValue::UInt8(value)
        | ProgramValue::UInt16(value)
        | ProgramValue::Int32(value)
        | ProgramValue::UInt32(value)
        | ProgramValue::Int64(value)
        | ProgramValue::UInt64(value)
        | ProgramValue::Int128(value)
        | ProgramValue::UInt128(value)
        | ProgramValue::Float32(value)
        | ProgramValue::Float64(value) => {
            collect_bitvector_integer_variables_seen(value, variables, seen)
        }
        ProgramValue::Pointer(_) | ProgramValue::Parameter(_) => {}
    }
}

fn collect_algebraic_integer_variables(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_algebraic_value_integer_variables(field, variables, seen);
            }
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_algebraic_value_integer_variables(
                &load_carrier(memory.shared_memory(), pointer),
                variables,
                seen,
            );
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_integer_variables(condition, variables, seen);
            collect_algebraic_integer_variables(then_term, variables, seen);
            collect_algebraic_integer_variables(else_term, variables, seen);
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_integer_variables(scrutinee, variables, seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_algebraic_value_integer_variables(binding, variables, seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_algebraic_integer_variables(&arm.body, variables, seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_pure_argument_integer_variables(argument, variables, seen);
            }
        }
    }
}

fn collect_algebraic_value_integer_variables(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        AlgebraicValue::Program(value) => {
            collect_program_value_integer_variables(value, variables, seen)
        }
        AlgebraicValue::Integer(value) => {
            collect_integer_carrier_variables_seen(value, variables, seen)
        }
        AlgebraicValue::Algebraic(value) => {
            collect_algebraic_integer_variables(value, variables, seen)
        }
    }
}

fn collect_integer_variables_seen(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if retained_folds::collect_native_fold_variables(
        term,
        retained_folds::FoldVariableRead::ExpressionFree,
        variables,
    ) {
        return;
    }

    crate::instrumentation::record_deterministic_work(1);
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                match argument {
                    PureFunctionArgument::SharedMachine(value) => {
                        collect_machine_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Value(value) => {
                        collect_program_value_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::Integer(value) => {
                        collect_shared_integer_variables(value, variables, seen)
                    }
                    PureFunctionArgument::Algebraic(value) => {
                        collect_algebraic_term_bitvector_variables(value, variables)
                    }
                    PureFunctionArgument::ArrayRef {
                        memory, pointer, ..
                    } => {
                        collect_memory_bitvector_variables(memory, variables);
                        collect_program_value_bitvector_variables(pointer, variables);
                    }
                }
            }
        }
        IntegerTerm::Machine(value) => match value.operand_view() {
            MachineOperandView::Legacy(value) => collect_bitvector_variables(value, variables),
            MachineOperandView::Shared(root) => {
                if let Some(leaves) =
                    shared_machine_conversion_leaves(root, || !checked_collection_checkpoint())
                {
                    for (_, leaf) in leaves.iter() {
                        if let KernelTermNode::Match(fold) = leaf.node() {
                            retained_matches::collect_match_variables(
                                fold,
                                retained_folds::FoldVariableRead::ExpressionFree,
                                variables,
                            );
                        } else if let KernelTermNode::Fold(fold) = leaf.node() {
                            retained_folds::collect_fold_variables(
                                fold,
                                retained_folds::FoldVariableRead::ExpressionFree,
                                variables,
                            );
                        } else if matches!(leaf.node(), KernelTermNode::FloatConvert { .. }) {
                            variables.extend(
                                retained_folds::common_variables(
                                    leaf,
                                    retained_folds::FoldVariableRead::ExpressionFree,
                                    &mut Default::default(),
                                )
                                .iter()
                                .copied(),
                            );
                        } else {
                            collect_bitvector_variables(
                                leaf.machine_conversion_leaf().expect("conversion leaf"),
                                variables,
                            );
                        }
                    }
                }
                if let Some(reads) =
                    shared_machine_read_leaves(root, || !checked_collection_checkpoint())
                {
                    for (_, read) in reads.iter() {
                        collect_operand_bitvector_variables(
                            MachineOperandView::Shared(read),
                            variables,
                        );
                    }
                }
                if let Some(written) =
                    shared_machine_syntax_variables(root, || !checked_collection_checkpoint())
                {
                    if EXECUTION_CEILING_ONLY.with(std::cell::Cell::get) {
                        // Only the maximum execution id is requested. The
                        // persistent syntax summary answers that by key; walking
                        // every prefix's variables would make admission quadratic.
                        variables.extend(
                            written
                                .get_less_than(&Variable(
                                    crate::kernel::ExecutionBudget::KERNEL_VARIABLE_CEILING,
                                ))
                                .copied(),
                        );
                        // Load names can hide execution ids in their live address
                        // and state. Resolve just those names with the ordinary
                        // leaf rule, never caching registry-dependent answers.
                        let range = crate::kernel::eval::LOAD_VARIABLE_RANGE;
                        let mut previous = Variable(range.start - 1);
                        while let Some(variable) = written.get_greater_than(&previous) {
                            if variable.0 >= range.end || checked_collection_checkpoint() {
                                break;
                            }
                            collect_bitvector_variables(
                                &MachineTerm::Variable(*variable),
                                variables,
                            );
                            previous = *variable;
                        }
                        return;
                    }
                    for variable in written.iter() {
                        if checked_collection_checkpoint() {
                            return;
                        }
                        // Preserve state deferral, connection and frame modes
                        // by using the ordinary variable-leaf collector.
                        collect_bitvector_variables(&MachineTerm::Variable(*variable), variables);
                    }
                }
            }
        },
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_variables(condition, variables);
            collect_shared_integer_variables(then_term, variables, seen);
            collect_shared_integer_variables(else_term, variables, seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_term_bitvector_variables(scrutinee, variables);
            for arm in arms {
                collect_shared_integer_variables(&arm.body, variables, seen);
            }
        }
        IntegerTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        IntegerTerm::Negate(value) => collect_shared_integer_variables(value, variables, seen),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_shared_integer_variables(left, variables, seen);
            collect_shared_integer_variables(right, variables, seen);
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                crate::kernel::IntegerRangeFoldIndex::Int32 { start, end }
                | crate::kernel::IntegerRangeFoldIndex::UInt64 { start, end } => {
                    collect_integer_variables_seen(
                        &IntegerTerm::Machine(start.machine_operand().clone()),
                        variables,
                        seen,
                    );
                    collect_integer_variables_seen(
                        &IntegerTerm::Machine(end.machine_operand().clone()),
                        variables,
                        seen,
                    );
                }
                crate::kernel::IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_variables(start, variables, seen);
                    collect_shared_integer_variables(end, variables, seen);
                }
            }
            collect_shared_integer_variables(initial, variables, seen);
            let mut body_variables = BTreeSet::new();
            collect_shared_integer_variables(body, &mut body_variables, &mut SeenTerms::default());
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
    }
}

fn collect_shared_integer_variables(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    seen: &mut SeenTerms,
) {
    if !seen.insert(term.id()) {
        return;
    }
    collect_integer_variables_seen(term, variables, seen);
}

fn collect_stored_load_connection_variables(
    memory: &SharedMemory,
    pointer: &Address,
    variables: &mut BTreeSet<Variable>,
) {
    if collecting_connection_variables() {
        // A written load depends on the value at its exact address,
        // rather than every value stored in the same state.
        struct Depth(usize);
        impl Drop for Depth {
            fn drop(&mut self) {
                CONNECTION_LOAD_DEPTH.with(|depth| depth.set(self.0));
            }
        }
        let depth = CONNECTION_LOAD_DEPTH.with(std::cell::Cell::get);
        if depth < HAVOC_RANGE_HOPS {
            let _scope = Depth(depth);
            CONNECTION_LOAD_DEPTH.with(|current| current.set(depth + 1));
            crate::instrumentation::record_deterministic_work(1);
            if let Some(value) = memory.memory().cells.explicitly_stored_value(pointer) {
                collect_program_value_bitvector_variables(value, variables);
            }
        }
    }
}

pub(crate) fn collect_bitvector_variables(term: &MachineTerm, variables: &mut BTreeSet<Variable>) {
    match term {
        MachineTerm::ThreadHandle(_) => {}
        MachineTerm::Constant { .. } => {}
        MachineTerm::Variable(variable) => {
            let newly_seen = variables.insert(*variable);
            if collecting_connection_variables() && !newly_seen {
                return;
            }
            // A load variable denotes its load, so the variables
            // of that load's address (a bound index, a loop counter) are
            // free in the term: a case split or substitution keyed on the
            // term's variables must see them.
            if crate::kernel::is_load_variable(variable)
                && let Some((memory, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                collect_shared_memory_bitvector_variables(&memory, variables);
                collect_pointer_bitvector_variables(&pointer, variables);
                collect_stored_load_connection_variables(&memory, &pointer, variables);
                if COLLECTING_HAVOC_RANGES.with(std::cell::Cell::get)
                    && let Some((origin, _)) =
                        crate::kernel::eval::registered_load_origin_for_variable(variable)
                {
                    // The canonical state may be a jumped placeholder.
                    // Frame dependencies belong to the live origin DAG.
                    collect_shared_memory_bitvector_variables(&origin, variables);
                }
            }
        }
        crate::kernel::binary_machine_term!(left, right)
        | MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            collect_bitvector_variables(left, variables);
            collect_bitvector_variables(right, variables);
        }
        crate::kernel::unary_machine_term!(value) => {
            collect_bitvector_variables(value, variables);
        }
        MachineTerm::BoolCast { value, .. } => {
            collect_condition_bitvector_variables(value, variables)
        }
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_bitvector_variables(condition, variables);
            collect_bitvector_variables(then_term, variables);
            collect_bitvector_variables(else_term, variables);
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_variables(start, variables);
            collect_bitvector_variables(end, variables);
            collect_bitvector_variables(initial, variables);
            let mut body_variables = BTreeSet::new();
            collect_bitvector_variables(body, &mut body_variables);
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_variables(argument, variables);
            }
        }
        MachineTerm::ClickFunctionApplication { arguments, .. } => {
            collect_application_connection_variables(arguments, variables);
        }
        MachineTerm::AlgebraicMatch {
            scrutinee, arms, ..
        } => {
            if collecting_connection_variables() {
                collect_algebraic_term_bitvector_variables(scrutinee, variables);
            }
            for arm in arms {
                collect_bitvector_variables(&arm.body, variables);
            }
        }
        MachineTerm::MemoryLoad(memory, pointer, _) => {
            collect_shared_memory_bitvector_variables(memory.shared_memory(), variables);
            collect_pointer_bitvector_variables(pointer, variables);
            collect_stored_load_connection_variables(memory.shared_memory(), pointer, variables);
            if COLLECTING_HAVOC_RANGES.with(std::cell::Cell::get)
                && let Some(origin) = crate::kernel::eval::scalar_read_observation(
                    crate::kernel::MachineOperandView::Legacy(term),
                )
                .and_then(|read| read.origin)
                && origin != *memory.shared_memory()
            {
                // Like a named read, a structural version can precede the
                // live DAG whose changed ranges the framing query needs.
                collect_shared_memory_bitvector_variables(&origin, variables);
            }
        }
        MachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_bitvector_variables(pointer, variables);
        }
        MachineTerm::IntegerToMachine { value, .. } => {
            let mut seen = SeenTerms::default();
            collect_shared_integer_variables(value, variables, &mut seen);
        }
    }
}

fn collect_bitvector_capture_variables_seen(
    term: &MachineTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        MachineTerm::ThreadHandle(_) => {}
        MachineTerm::Constant { .. } => {}
        MachineTerm::Variable(variable) => {
            variables.insert(*variable);
            if crate::kernel::is_load_variable(variable)
                && let Some((_, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                collect_pointer_capture_variables(&pointer, variables, integer_seen);
            }
        }
        crate::kernel::binary_machine_term!(left, right)
        | MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            collect_bitvector_capture_variables_seen(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(right, variables, integer_seen);
        }
        crate::kernel::unary_machine_term!(value) => {
            collect_bitvector_capture_variables_seen(value, variables, integer_seen)
        }
        MachineTerm::BoolCast { value, .. } => {
            collect_condition_capture_variables(value, variables, integer_seen)
        }
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_capture_variables(condition, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(then_term, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(else_term, variables, integer_seen);
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_capture_variables_seen(start, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(end, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(initial, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            let mut body_variables = BTreeSet::new();
            collect_bitvector_capture_variables_seen(
                body,
                &mut body_variables,
                &mut SeenTerms::default(),
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            body_variables.remove(accumulator);
            body_variables.remove(item);
            variables.extend(body_variables);
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_capture_variables_seen(argument, variables, integer_seen);
            }
        }
        MachineTerm::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
            }
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_capture_variables_in_algebraic_term(scrutinee, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_capture_variables_in_algebraic_value(binding, variables, integer_seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_capture_variables_seen(&arm.body, variables, integer_seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        MachineTerm::MemoryLoad(_, pointer, _) | MachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_capture_variables(pointer, variables, integer_seen)
        }
        MachineTerm::IntegerToMachine { value, .. } => {
            collect_shared_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
    }
}

/// The address-base and bitvector variables a proposition captures,
/// including the pointers inside pure-function arguments, which the plain
/// bitvector collection does not descend into. Conditions and their
/// connectives are traversed with the capture walk; any other proposition
/// shape falls back to [`collect_proposition_bitvector_variables`].
pub(in crate::kernel) fn collect_proposition_capture_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = SeenTerms::default();
    let mut condition_summaries = Default::default();
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            Proposition::ConditionIs(condition, _) => {
                if let Some(root) = condition.root() {
                    variables.extend(
                        retained_folds::common_variables(
                            root,
                            retained_folds::FoldVariableRead::MachineCapture,
                            &mut condition_summaries,
                        )
                        .iter()
                        .copied(),
                    );
                } else {
                    collect_condition_capture_variables(
                        condition.native_compat(),
                        variables,
                        &mut integer_seen,
                    );
                }
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            Proposition::Not(body) => pending.push(body),
            proposition => collect_proposition_bitvector_variables(proposition, variables),
        }
    }
}

fn collect_condition_capture_variables(
    condition: &ConditionTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_capture_variables(pointer, variables, integer_seen);
            }
        }

        ConditionTerm::Constant(_) => {}
        ConditionTerm::Variable(variable) => {
            variables.insert(*variable);
        }
        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_capture_variables_in_algebraic_term(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_capture_variables_in_algebraic_term(right, variables, integer_seen);
        }
        crate::kernel::binary_bitvector_condition!(left, right) => {
            collect_bitvector_capture_variables_seen(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_capture_variables_seen(right, variables, integer_seen);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| {
                if !crate::instrumentation::checked_collection_exhausted() {
                    collect_bitvector_capture_variables_seen(term, variables, integer_seen)
                }
            });
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_capture_variables(right, variables, integer_seen);
        }
        ConditionTerm::AddressEqual(left, right) => {
            collect_pointer_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_capture_variables(right, variables, integer_seen);
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_shared_integer_bitvector_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(right, variables, integer_seen);
        }
        ConditionTerm::BoolApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
            }
        }
        ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => {
            for child in condition.bool_children() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_condition_capture_variables(child, variables, integer_seen);
            }
        }
        ConditionTerm::BoolLoad(_, pointer) => {
            collect_pointer_capture_variables(pointer, variables, integer_seen)
        }
    }
}

fn collect_pointer_offset_capture_variables(
    offset: &AddressOffset,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match offset {
        AddressOffset::Constant(_) | AddressOffset::Variable(_) => {}
        AddressOffset::Add(left, right) => {
            collect_pointer_offset_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_capture_variables(right, variables, integer_seen);
        }
        AddressOffset::Int32Scaled { value, .. } | AddressOffset::Int64Scaled { value, .. } => {
            visit_machine_carrier_leaves(value, |leaf| {
                if let Some((_, pointer, _)) = leaf.read() {
                    collect_pointer_capture_variables(pointer, variables, integer_seen);
                } else if let MachineOperandView::Legacy(term) = leaf {
                    collect_bitvector_capture_variables_seen(term, variables, integer_seen);
                }
            });
        }
    }
}

fn collect_pointer_capture_variables(
    pointer: &Address,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &pointer.base {
        AddressBase::PureFunctionApplication(application) => {
            if integer_seen.pointers.insert(application.id()) {
                for argument in application.arguments() {
                    collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
                }
            }
        }
        AddressBase::Symbolic(variable)
        | AddressBase::FunctionSymbolic(variable)
        | AddressBase::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        AddressBase::ContractResult | AddressBase::ContractException | AddressBase::AggregateReturn { .. } | AddressBase::StaticObject { .. } | AddressBase::AutomaticLocal { .. } | AddressBase::ReferenceCarrier { .. } | AddressBase::Concrete(_)
        | AddressBase::StringLiteral { .. }
        | AddressBase::Function(_)
        | AddressBase::ExternalArgument
        // The identity is opaque here, like a scalar load name. The equality
        // graph separately indexes its defining address exactly once.
        | AddressBase::LoadedPointer(_)
        | AddressBase::Heap(_)
        | AddressBase::Temporary(_) => {}
    }
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    collect_pointer_offset_capture_variables(&pointer.offset, variables, integer_seen);
}

fn collect_capture_variables_in_program_value(
    value: &ProgramValue,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        ProgramValue::PointerInteger(record) => {
            collect_capture_variables_in_program_value(&record.numeric, variables, integer_seen);
            collect_capture_variables_in_program_value(
                &ProgramValue::Pointer(*record.pointer.clone()),
                variables,
                integer_seen,
            );
        }
        ProgramValue::Parameter(term) => {
            collect_capture_variables_in_algebraic_term(term, variables, integer_seen)
        }
        ProgramValue::Void => {}
        ProgramValue::Int8(bits) => {
            collect_bitvector_capture_variables_seen(bits, variables, integer_seen)
        }
        ProgramValue::Bool(bits)
        | ProgramValue::Int16(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt32(bits)
        | ProgramValue::Int64(bits)
        | ProgramValue::UInt64(bits)
        | ProgramValue::Int128(bits)
        | ProgramValue::UInt128(bits)
        | ProgramValue::Float32(bits)
        | ProgramValue::Float64(bits) => {
            collect_bitvector_capture_variables_seen(bits, variables, integer_seen)
        }
        ProgramValue::Pointer(pointer) => {
            for address in pointer.pointers() {
                collect_pointer_capture_variables(address, variables, integer_seen);
            }
        }
    }
}

fn collect_capture_variables_in_pure_argument(
    argument: &PureFunctionArgument,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match argument {
        PureFunctionArgument::SharedMachine(value) => {
            collect_integer_bitvector_capture_variables(
                &IntegerTerm::Machine(value.clone()),
                variables,
                integer_seen,
            );
        }
        PureFunctionArgument::Value(value) => {
            collect_capture_variables_in_program_value(value, variables, integer_seen)
        }
        PureFunctionArgument::Integer(value) => {
            collect_shared_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_capture_variables_in_algebraic_term(value, variables, integer_seen)
        }
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_capture_variables_in_program_value(pointer, variables, integer_seen)
        }
    }
}

fn collect_capture_variables_in_algebraic_term(
    term: &AlgebraicTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_algebraic_value(field, variables, integer_seen);
            }
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_capture_variables_in_algebraic_value(
                &load_carrier(memory.shared_memory(), pointer),
                variables,
                integer_seen,
            );
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_capture_variables(condition, variables, integer_seen);
            collect_capture_variables_in_algebraic_term(then_term, variables, integer_seen);
            collect_capture_variables_in_algebraic_term(else_term, variables, integer_seen);
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_capture_variables_in_algebraic_term(scrutinee, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_capture_variables_in_algebraic_value(binding, variables, integer_seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_algebraic_term(&arm.body, variables, integer_seen);
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
            }
        }
    }
}

fn collect_capture_variables_in_algebraic_value(
    value: &AlgebraicValue,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        AlgebraicValue::Program(value) => {
            collect_capture_variables_in_program_value(value, variables, integer_seen)
        }
        AlgebraicValue::Integer(value) => {
            collect_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
        AlgebraicValue::Algebraic(value) => {
            collect_capture_variables_in_algebraic_term(value, variables, integer_seen)
        }
    }
}

fn collect_shared_integer_bitvector_capture_variables(
    term: &SharedIntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    if integer_seen.insert(term.id()) {
        collect_integer_bitvector_capture_variables(term.as_ref(), variables, integer_seen);
    }
}

fn collect_integer_bitvector_capture_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if retained_folds::collect_native_fold_variables(
        term,
        retained_folds::FoldVariableRead::MachineCapture,
        variables,
    ) {
        return;
    }

    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => {}
        IntegerTerm::Machine(value) => match value.operand_view() {
            MachineOperandView::Legacy(value) => {
                collect_bitvector_capture_variables_seen(value, variables, integer_seen)
            }
            MachineOperandView::Shared(root) => {
                if let Some(leaves) =
                    shared_machine_conversion_leaves(root, || !checked_collection_checkpoint())
                {
                    for (_, leaf) in leaves.iter() {
                        if let KernelTermNode::Match(fold) = leaf.node() {
                            retained_matches::collect_match_variables(
                                fold,
                                retained_folds::FoldVariableRead::MachineCapture,
                                variables,
                            );
                        } else if let KernelTermNode::Fold(fold) = leaf.node() {
                            retained_folds::collect_fold_variables(
                                fold,
                                retained_folds::FoldVariableRead::MachineCapture,
                                variables,
                            );
                        } else if matches!(leaf.node(), KernelTermNode::FloatConvert { .. }) {
                            variables.extend(
                                retained_folds::common_variables(
                                    leaf,
                                    retained_folds::FoldVariableRead::MachineCapture,
                                    &mut Default::default(),
                                )
                                .iter()
                                .copied(),
                            );
                        } else {
                            collect_bitvector_capture_variables_seen(
                                leaf.machine_conversion_leaf().expect("conversion leaf"),
                                variables,
                                integer_seen,
                            );
                        }
                    }
                }
                if let Some(reads) =
                    shared_machine_read_leaves(root, || !checked_collection_checkpoint())
                {
                    for (_, read) in reads.iter() {
                        let (_, pointer, _) =
                            MachineOperandView::Shared(read).read().expect("read leaf");
                        collect_pointer_capture_variables(pointer, variables, integer_seen);
                    }
                }
                if let Some(written) =
                    shared_machine_syntax_variables(root, || !checked_collection_checkpoint())
                {
                    for variable in written.iter() {
                        if checked_collection_checkpoint() {
                            return;
                        }
                        // A registered load's pointer can capture the binder.
                        // Keep the ordinary leaf rule after traversing the DAG.
                        collect_bitvector_capture_variables_seen(
                            &MachineTerm::Variable(*variable),
                            variables,
                            integer_seen,
                        );
                    }
                }
            }
        },
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_capture_variables_in_pure_argument(argument, variables, integer_seen);
            }
        }
        IntegerTerm::Negate(value) => {
            collect_shared_integer_bitvector_capture_variables(value, variables, integer_seen)
        }
        crate::kernel::binary_integer_term!(left, right) => {
            collect_shared_integer_bitvector_capture_variables(left, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(right, variables, integer_seen);
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_capture_variables(condition, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(then_term, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(else_term, variables, integer_seen);
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_capture_variables_in_algebraic_term(scrutinee, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_capture_variables_in_algebraic_value(binding, variables, integer_seen);
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_shared_integer_bitvector_capture_variables(
                    &arm.body,
                    variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            item,
            body,
            ..
        } => {
            match index {
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    collect_integer_bitvector_capture_variables(
                        &IntegerTerm::Machine(start.machine_operand().clone()),
                        variables,
                        integer_seen,
                    );
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_integer_bitvector_capture_variables(
                        &IntegerTerm::Machine(end.machine_operand().clone()),
                        variables,
                        integer_seen,
                    );
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_shared_integer_bitvector_capture_variables(
                        start,
                        variables,
                        integer_seen,
                    );
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_shared_integer_bitvector_capture_variables(
                        end,
                        variables,
                        integer_seen,
                    );
                }
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_shared_integer_bitvector_capture_variables(initial, variables, integer_seen);
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            if index.machine_item_type().is_some() {
                let mut body_variables = BTreeSet::new();
                collect_shared_integer_bitvector_capture_variables(
                    body,
                    &mut body_variables,
                    &mut SeenTerms::default(),
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                body_variables.remove(item);
                variables.extend(body_variables);
            } else {
                collect_shared_integer_bitvector_capture_variables(body, variables, integer_seen);
            }
        }
    }
}

/// Collect C-carrier variables nested in an Integer term without descending
/// into memory states.  Machine conversions and opaque pure arguments are
/// part of the lexical expression and therefore remain visible to capture
/// analysis.
pub(crate) fn collect_integer_capture_bitvector_variables(
    term: &IntegerTerm,
    variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = SeenTerms::default();
    collect_integer_bitvector_capture_variables(term, variables, &mut integer_seen);
}

/// The carrier-separated free-variable summary used by capture-avoiding
/// Integer rewrites.  `max` includes both free variables and nested fold
/// binders, so a fresh binder cannot collide with a name that is protected
/// deeper in the same DAG.
#[derive(Clone, Debug, Default)]
pub(crate) struct IntegerScopeSummary {
    pub(crate) max: u64,
}

impl IntegerScopeSummary {
    fn merge(&mut self, other: Self) {
        self.max = self.max.max(other.max);
    }

    fn integer_variable(variable: Variable) -> Self {
        Self { max: variable.0 }
    }

    fn bitvector_variable(variable: Variable) -> Self {
        Self { max: variable.0 }
    }

    fn reserve(&mut self, variable: Variable) {
        self.max = self.max.max(variable.0);
    }
}

/// Collect summaries for an Integer DAG in one shared traversal.  The map is
/// populated for every shared Integer node reached from `term`, so later
/// nested-fold scopes reuse their already-computed suffix summary instead of
/// recursively scanning that suffix again.
pub(crate) fn collect_integer_scope_summaries(
    term: &SharedIntegerTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    collect_integer_scope_summary_shared(term, summaries)
}

fn collect_integer_scope_summary_shared(
    term: &SharedIntegerTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if crate::instrumentation::checked_collection_exhausted() {
        return IntegerScopeSummary::default();
    }
    if let Some(summary) = summaries.get(&term.id()) {
        return summary.clone();
    }
    let summary = collect_integer_scope_summary(term.as_ref(), summaries);
    summaries.insert(term.id(), summary.clone());
    summary
}

fn collect_machine_scope_summary(
    machine: &SharedMachineIntegerTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    collect_machine_operand_scope_summary(machine.operand_view(), summaries)
}

fn collect_machine_operand_scope_summary(
    operand: MachineOperandView<'_>,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    let MachineOperandView::Shared(root) = operand else {
        let MachineOperandView::Legacy(term) = operand else {
            unreachable!()
        };
        return collect_bitvector_scope_summary(term, summaries);
    };
    if let Some(variable) = operand.variable() {
        return collect_bitvector_scope_summary(&MachineTerm::Variable(*variable), summaries);
    }
    if let Some((_, pointer, _)) = operand.read() {
        return collect_pointer_scope_summary(pointer, summaries);
    }
    if operand.literal().is_some() {
        return IntegerScopeSummary::default();
    }
    if let Some(leaf) = root.machine_conversion_leaf() {
        return collect_bitvector_scope_summary(leaf, summaries);
    }
    if let KernelTermNode::Fold(fold) = root.node() {
        return collect_fold_scope_summary(fold, summaries);
    }
    if matches!(root.node(), KernelTermNode::FloatConvert { .. }) {
        return collect_bitvector_scope_summary(
            &KernelTermExport::machine(root).expect("float conversion"),
            summaries,
        );
    }
    let mut summary = IntegerScopeSummary::default();
    if let Some(leaves) =
        shared_machine_conversion_leaves(root, || !checked_collection_checkpoint())
    {
        for (_, leaf) in leaves.iter() {
            if checked_collection_checkpoint() {
                return IntegerScopeSummary::default();
            }
            summary.merge(if let KernelTermNode::Fold(fold) = leaf.node() {
                collect_fold_scope_summary(fold, summaries)
            } else if matches!(leaf.node(), KernelTermNode::FloatConvert { .. }) {
                collect_bitvector_scope_summary(
                    &KernelTermExport::machine(leaf).expect("float conversion"),
                    summaries,
                )
            } else {
                collect_bitvector_scope_summary(
                    leaf.machine_conversion_leaf().expect("conversion leaf"),
                    summaries,
                )
            });
        }
    }
    if let Some(reads) = shared_machine_read_leaves(root, || !checked_collection_checkpoint()) {
        for (_, read) in reads.iter() {
            let (_, pointer, _) = MachineOperandView::Shared(read).read().expect("read leaf");
            summary.merge(collect_pointer_scope_summary(pointer, summaries));
        }
    }
    if let Some(written) =
        shared_machine_syntax_variables(root, || !checked_collection_checkpoint())
    {
        // The caller needs one maximum, not every arithmetic variable. Growing
        // prefixes must not repeatedly enumerate their complete variable sets.
        if let Some(variable) = written.last() {
            summary.reserve(*variable);
        }
        let range = crate::kernel::eval::LOAD_VARIABLE_RANGE;
        let mut previous = Variable(range.start - 1);
        while let Some(variable) = written.get_greater_than(&previous) {
            if variable.0 >= range.end || checked_collection_checkpoint() {
                break;
            }
            summary.merge(collect_bitvector_scope_summary(
                &MachineTerm::Variable(*variable),
                summaries,
            ));
            previous = *variable;
        }
    }
    summary
}

fn collect_fold_scope_summary(
    fold: &KernelFold,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    let mut result = IntegerScopeSummary::default();
    for child in &fold.arguments {
        let value = SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, child.clone())
            .expect("machine fold operand");
        result.merge(collect_machine_scope_summary(&value, summaries));
    }
    result.reserve(fold.accumulator);
    result.reserve(fold.item);
    result
}

fn collect_integer_scope_summary(
    term: &IntegerTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match term {
        IntegerTerm::Constant(_) => IntegerScopeSummary::default(),
        IntegerTerm::Variable(variable) => IntegerScopeSummary::integer_variable(*variable),
        IntegerTerm::Machine(value) => collect_machine_scope_summary(value, summaries),
        IntegerTerm::Negate(value) => collect_integer_scope_summary_shared(value, summaries),
        crate::kernel::binary_integer_term!(left, right) => {
            let mut summary = collect_integer_scope_summary_shared(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(right, summaries));
            summary
        }
        IntegerTerm::PureFunctionApplication(application) => {
            let mut summary = IntegerScopeSummary::default();
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_scope_summary_in_argument(argument, summaries));
            }
            summary
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            let mut summary = collect_condition_scope_summary(condition, summaries);
            summary.merge(collect_integer_scope_summary_shared(then_term, summaries));
            summary.merge(collect_integer_scope_summary_shared(else_term, summaries));
            summary
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            let mut summary = collect_algebraic_scope_summary(scrutinee, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_algebraic_value_scope_summary(binding, summaries));
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_integer_scope_summary_shared(&arm.body, summaries));
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
            }
            summary
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut summary = match index {
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    let mut summary =
                        collect_machine_scope_summary(start.machine_operand(), summaries);
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_machine_scope_summary(
                        end.machine_operand(),
                        summaries,
                    ));
                    summary
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    let mut summary = collect_integer_scope_summary_shared(start, summaries);
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_integer_scope_summary_shared(end, summaries));
                    summary
                }
            };
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(initial, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(body, summaries));
            summary.reserve(*accumulator);
            summary.reserve(*item);
            summary
        }
    }
}

fn collect_bitvector_scope_summary(
    term: &MachineTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match term {
        MachineTerm::ThreadHandle(_) => IntegerScopeSummary::default(),
        MachineTerm::Constant { .. } => IntegerScopeSummary::default(),
        MachineTerm::Variable(variable) => {
            let mut summary = IntegerScopeSummary::bitvector_variable(*variable);
            if crate::kernel::is_load_variable(variable)
                && let Some((_, pointer)) =
                    crate::kernel::eval::registered_load_for_variable(variable)
            {
                summary.merge(collect_pointer_scope_summary(&pointer, summaries));
            }
            summary
        }
        crate::kernel::binary_machine_term!(left, right)
        | MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            let mut summary = collect_bitvector_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(right, summaries));
            summary
        }
        crate::kernel::unary_machine_term!(value) => {
            collect_bitvector_scope_summary(value, summaries)
        }
        MachineTerm::BoolCast { value, .. } => collect_condition_scope_summary(value, summaries),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            let mut summary = collect_condition_scope_summary(condition, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(then_term, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(else_term, summaries));
            summary
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let mut summary = collect_bitvector_scope_summary(start, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(end, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(initial, summaries));
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(body, summaries));
            summary.reserve(*accumulator);
            summary.reserve(*item);
            summary
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_bitvector_scope_summary(argument, summaries));
            }
            summary
        }
        MachineTerm::ClickFunctionApplication { arguments, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_scope_summary_in_argument(argument, summaries));
            }
            summary
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => {
            let mut summary = collect_algebraic_scope_summary(scrutinee, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_algebraic_value_scope_summary(binding, summaries));
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_bitvector_scope_summary(&arm.body, summaries));
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
            }
            summary
        }
        MachineTerm::MemoryLoad(_, pointer, _) | MachineTerm::IntegerAddress(pointer, _) => {
            collect_pointer_scope_summary(pointer, summaries)
        }
        MachineTerm::IntegerToMachine { value, .. } => {
            collect_integer_scope_summary_shared(value, summaries)
        }
    }
}

fn collect_pointer_scope_summary(
    pointer: &Address,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    let mut summary = match &pointer.base {
        AddressBase::Symbolic(variable)
        | AddressBase::FunctionSymbolic(variable)
        | AddressBase::ExternalObject(variable) => {
            IntegerScopeSummary::bitvector_variable(*variable)
        }
        _ => IntegerScopeSummary::default(),
    };
    summary.merge(collect_pointer_offset_scope_summary(
        &pointer.offset,
        summaries,
    ));
    summary
}

fn collect_pointer_offset_scope_summary(
    offset: &AddressOffset,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match offset {
        AddressOffset::Constant(_) | AddressOffset::Variable(_) => IntegerScopeSummary::default(),
        AddressOffset::Add(left, right) => {
            let mut summary = collect_pointer_offset_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_pointer_offset_scope_summary(right, summaries));
            summary
        }
        AddressOffset::Int32Scaled { value, .. } | AddressOffset::Int64Scaled { value, .. } => {
            collect_machine_scope_summary(value, summaries)
        }
    }
}

fn collect_condition_scope_summary(
    condition: &ConditionTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            let mut summary = IntegerScopeSummary::default();
            for pointer in left.pointers().chain(right.pointers()) {
                summary.merge(collect_pointer_scope_summary(pointer, summaries));
            }
            summary
        }

        ConditionTerm::Constant(_) => IntegerScopeSummary::default(),
        ConditionTerm::Variable(variable) => IntegerScopeSummary::bitvector_variable(*variable),
        ConditionTerm::AlgebraicEqual(left, right) => {
            let mut summary = collect_algebraic_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_algebraic_scope_summary(right, summaries));
            summary
        }
        crate::kernel::binary_bitvector_condition!(left, right) => {
            let mut summary = collect_bitvector_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_bitvector_scope_summary(right, summaries));
            summary
        }
        ConditionTerm::Float32(condition) | ConditionTerm::Float64(condition) => {
            let mut summary = IntegerScopeSummary::default();
            condition.for_each_bitvector_term(|term| {
                if !crate::instrumentation::checked_collection_exhausted() {
                    summary.merge(collect_bitvector_scope_summary(term, summaries));
                }
            });
            summary
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            let mut summary = collect_pointer_offset_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_pointer_offset_scope_summary(right, summaries));
            summary
        }
        ConditionTerm::AddressEqual(left, right) => {
            let mut summary = collect_pointer_scope_summary(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_pointer_scope_summary(right, summaries));
            summary
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            let mut summary = collect_integer_scope_summary_shared(left, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            summary.merge(collect_integer_scope_summary_shared(right, summaries));
            summary
        }
        ConditionTerm::BoolApplication(application) => {
            let mut summary = IntegerScopeSummary::default();
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_scope_summary_in_argument(argument, summaries));
            }
            summary
        }
        ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => {
            let mut summary = IntegerScopeSummary::default();
            for child in condition.bool_children() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_condition_scope_summary(child, summaries));
            }
            summary
        }
        ConditionTerm::BoolLoad(_, pointer) => collect_pointer_scope_summary(pointer, summaries),
    }
}

fn collect_scope_summary_in_argument(
    argument: &PureFunctionArgument,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match argument {
        PureFunctionArgument::SharedMachine(value) => {
            collect_machine_scope_summary(value, summaries)
        }
        PureFunctionArgument::Value(value) => collect_program_value_scope_summary(value, summaries),
        PureFunctionArgument::Integer(value) => {
            collect_integer_scope_summary_shared(value, summaries)
        }
        PureFunctionArgument::Algebraic(value) => collect_algebraic_scope_summary(value, summaries),
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_program_value_scope_summary(pointer, summaries)
        }
    }
}

fn collect_program_value_scope_summary(
    value: &ProgramValue,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match value {
        ProgramValue::PointerInteger(record) => {
            let mut summary = collect_program_value_scope_summary(&record.numeric, summaries);
            summary.merge(collect_program_value_scope_summary(
                &ProgramValue::Pointer(*record.pointer.clone()),
                summaries,
            ));
            summary
        }
        ProgramValue::Parameter(term) => collect_algebraic_scope_summary(term, summaries),
        ProgramValue::Void => IntegerScopeSummary::default(),
        ProgramValue::Int8(term) => collect_bitvector_scope_summary(term, summaries),
        ProgramValue::Bool(term)
        | ProgramValue::Int16(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term)
        | ProgramValue::Float32(term)
        | ProgramValue::Float64(term) => collect_bitvector_scope_summary(term, summaries),
        ProgramValue::Pointer(pointer) => {
            let mut summary = IntegerScopeSummary::default();
            for address in pointer.pointers() {
                summary.merge(collect_pointer_scope_summary(address, summaries));
            }
            summary
        }
    }
}

fn collect_algebraic_scope_summary(
    term: &AlgebraicTerm,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => IntegerScopeSummary::default(),
        AlgebraicTermNode::Constructor { fields, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_algebraic_value_scope_summary(field, summaries));
            }
            summary
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => collect_algebraic_value_scope_summary(
            &load_carrier(memory.shared_memory(), pointer),
            summaries,
        ),
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            let mut summary = collect_condition_scope_summary(condition, summaries);
            summary.merge(collect_algebraic_scope_summary(then_term, summaries));
            summary.merge(collect_algebraic_scope_summary(else_term, summaries));
            summary
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            let mut summary = collect_algebraic_scope_summary(scrutinee, summaries);
            if crate::instrumentation::checked_collection_exhausted() {
                return IntegerScopeSummary::default();
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return IntegerScopeSummary::default();
                    }
                    summary.merge(collect_algebraic_value_scope_summary(binding, summaries));
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_algebraic_scope_summary(&arm.body, summaries));
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
            }
            summary
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            let mut summary = IntegerScopeSummary::default();
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return IntegerScopeSummary::default();
                }
                summary.merge(collect_scope_summary_in_argument(argument, summaries));
            }
            summary
        }
    }
}

fn collect_algebraic_value_scope_summary(
    value: &AlgebraicValue,
    summaries: &mut std::collections::HashMap<u64, IntegerScopeSummary>,
) -> IntegerScopeSummary {
    if checked_collection_checkpoint() {
        return IntegerScopeSummary::default();
    }
    match value {
        AlgebraicValue::Program(value) => collect_program_value_scope_summary(value, summaries),
        AlgebraicValue::Integer(value) => collect_integer_scope_summary(value, summaries),
        AlgebraicValue::Algebraic(value) => collect_algebraic_scope_summary(value, summaries),
    }
}

/// Collect only fold binder names from an Integer expression, keeping the
/// Integer and C carriers separate.  Capture analysis must remove nested
/// binders, while fresh-name selection must reserve them: otherwise a fresh C
/// item can accidentally reuse the name of a deeper fold in the body.
pub(crate) fn collect_integer_binder_variables(
    term: &IntegerTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
) {
    let mut integer_seen = SeenTerms::default();
    collect_integer_binder_variables_seen(
        term,
        integer_variables,
        bitvector_variables,
        &mut integer_seen,
    );
}

fn collect_integer_binder_variables_seen(
    term: &IntegerTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => {}
        IntegerTerm::Machine(value) => visit_machine_carrier_leaves(value, |leaf| {
            collect_operand_binder_variables_seen(
                leaf,
                integer_variables,
                bitvector_variables,
                integer_seen,
            )
        }),
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_pure_argument(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        IntegerTerm::Negate(value) => collect_integer_binder_variables_shared(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        crate::kernel::binary_integer_term!(left, right) => {
            collect_integer_binder_variables_shared(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        IntegerTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_binder_variables(
                condition,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            for branch in [then_term, else_term] {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_integer_binder_variables_shared(
                    branch,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_binder_variables_in_algebraic_term(
                scrutinee,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_binder_variables_in_algebraic_value(
                        binding,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_integer_binder_variables_shared(
                    &arm.body,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            integer_variables.insert(*accumulator);
            match index {
                IntegerRangeFoldIndex::Int32 { start, end }
                | IntegerRangeFoldIndex::UInt64 { start, end } => {
                    bitvector_variables.insert(*item);
                    visit_machine_carrier_leaves(start.machine_operand(), |leaf| {
                        collect_operand_binder_variables_seen(
                            leaf,
                            integer_variables,
                            bitvector_variables,
                            integer_seen,
                        )
                    });
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    visit_machine_carrier_leaves(end.machine_operand(), |leaf| {
                        collect_operand_binder_variables_seen(
                            leaf,
                            integer_variables,
                            bitvector_variables,
                            integer_seen,
                        )
                    });
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    integer_variables.insert(*item);
                    collect_integer_binder_variables_shared(
                        start,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_integer_binder_variables_shared(
                        end,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
            }
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                initial,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                body,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
    }
}

fn collect_integer_binder_variables_shared(
    term: &SharedIntegerTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if crate::instrumentation::checked_collection_exhausted() {
        return;
    }
    if integer_seen.insert(term.id()) {
        collect_integer_binder_variables_seen(
            term.as_ref(),
            integer_variables,
            bitvector_variables,
            integer_seen,
        );
    }
}

fn collect_bitvector_binder_variables_seen(
    term: &MachineTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match term {
        MachineTerm::ThreadHandle(_) => {}
        MachineTerm::Constant { .. }
        | MachineTerm::Variable(_)
        | MachineTerm::MemoryLoad(_, _, _)
        | MachineTerm::IntegerAddress(_, _) => {}
        MachineTerm::IntegerToMachine { value, .. } => {
            collect_integer_binder_variables_shared(
                value,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        crate::kernel::binary_machine_term!(left, right)
        | MachineTerm::Float32Binary { left, right, .. }
        | MachineTerm::Float64Binary { left, right, .. } => {
            collect_bitvector_binder_variables_seen(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        crate::kernel::unary_machine_term!(value) => {
            collect_bitvector_binder_variables_seen(
                value,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        MachineTerm::BoolCast { value, .. } => collect_condition_binder_variables(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_binder_variables(
                condition,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                then_term,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                else_term,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            bitvector_variables.insert(*accumulator);
            bitvector_variables.insert(*item);
            collect_bitvector_binder_variables_seen(
                start,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                end,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                initial,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                body,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        MachineTerm::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_binder_variables_seen(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        MachineTerm::ClickFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_pure_argument(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        MachineTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_binder_variables_in_algebraic_term(
                scrutinee,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_binder_variables_in_algebraic_value(
                        binding,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_bitvector_binder_variables_seen(
                    &arm.body,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
    }
}

fn collect_condition_binder_variables(
    condition: &ConditionTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match condition {
        ConditionTerm::PointerEqual(left, right) => {
            for pointer in left.pointers().chain(right.pointers()) {
                collect_pointer_binder_variables(
                    pointer,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }

        ConditionTerm::AlgebraicEqual(left, right) => {
            collect_binder_variables_in_algebraic_term(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_binder_variables_in_algebraic_term(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        crate::kernel::binary_bitvector_condition!(left, right) => {
            collect_bitvector_binder_variables_seen(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_bitvector_binder_variables_seen(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| {
                if !crate::instrumentation::checked_collection_exhausted() {
                    collect_bitvector_binder_variables_seen(
                        term,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    )
                }
            });
        }
        ConditionTerm::AddressOffsetEqual(left, right) => {
            collect_pointer_offset_binder_variables(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_binder_variables(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ConditionTerm::AddressEqual(left, right) => {
            collect_pointer_binder_variables(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_binder_variables(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        crate::kernel::integer_comparison_condition!(left, right) => {
            collect_integer_binder_variables_shared(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_integer_binder_variables_shared(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        ConditionTerm::BoolApplication(application) => {
            for argument in application.arguments() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_pure_argument(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        ConditionTerm::BoolIf { .. } | ConditionTerm::BoolEqual(..) => {
            for child in condition.bool_children() {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_condition_binder_variables(
                    child,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        // As a word-valued load: a read binds nothing.
        ConditionTerm::BoolLoad(..) => {}
    }
}

fn collect_pointer_offset_binder_variables(
    offset: &AddressOffset,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match offset {
        AddressOffset::Constant(_) | AddressOffset::Variable(_) => {}
        AddressOffset::Add(left, right) => {
            collect_pointer_offset_binder_variables(
                left,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            collect_pointer_offset_binder_variables(
                right,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        AddressOffset::Int32Scaled { value, .. } | AddressOffset::Int64Scaled { value, .. } => {
            visit_machine_carrier_leaves(value, |leaf| {
                collect_operand_binder_variables_seen(
                    leaf,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            });
        }
    }
}

fn collect_pointer_binder_variables(
    pointer: &Address,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    if let AddressBase::PureFunctionApplication(application) = &pointer.base
        && integer_seen.pointers.insert(application.id())
    {
        for argument in application.arguments() {
            collect_binder_variables_in_pure_argument(
                argument,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
    }
    collect_pointer_offset_binder_variables(
        &pointer.offset,
        integer_variables,
        bitvector_variables,
        integer_seen,
    );
}

fn collect_binder_variables_in_program_value(
    value: &ProgramValue,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        ProgramValue::PointerInteger(record) => {
            collect_binder_variables_in_program_value(
                &record.numeric,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            collect_binder_variables_in_program_value(
                &ProgramValue::Pointer(*record.pointer.clone()),
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        ProgramValue::Parameter(term) => collect_binder_variables_in_algebraic_term(
            term,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        ProgramValue::Void => {}
        ProgramValue::Int8(bits) => collect_bitvector_binder_variables_seen(
            bits,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        ProgramValue::Bool(bits)
        | ProgramValue::Int16(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt32(bits)
        | ProgramValue::Int64(bits)
        | ProgramValue::UInt64(bits)
        | ProgramValue::Int128(bits)
        | ProgramValue::UInt128(bits)
        | ProgramValue::Float32(bits)
        | ProgramValue::Float64(bits) => collect_bitvector_binder_variables_seen(
            bits,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        ProgramValue::Pointer(pointer) => {
            for address in pointer.pointers() {
                collect_pointer_binder_variables(
                    address,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
    }
}

fn collect_binder_variables_in_pure_argument(
    argument: &PureFunctionArgument,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match argument {
        PureFunctionArgument::SharedMachine(value) => visit_machine_carrier_leaves(value, |leaf| {
            collect_operand_binder_variables_seen(
                leaf,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }),
        PureFunctionArgument::Value(value) => collect_binder_variables_in_program_value(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        PureFunctionArgument::Integer(value) => collect_integer_binder_variables_shared(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        PureFunctionArgument::Algebraic(value) => collect_binder_variables_in_algebraic_term(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        PureFunctionArgument::ArrayRef { pointer, .. } => {
            collect_binder_variables_in_program_value(
                pointer,
                integer_variables,
                bitvector_variables,
                integer_seen,
            )
        }
    }
}

fn collect_binder_variables_in_algebraic_term(
    term: &AlgebraicTerm,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(_) => {}
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_algebraic_value(
                    field,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
        AlgebraicTermNode::MemoryLoad {
            point: memory,
            pointer,
        } => {
            collect_binder_variables_in_algebraic_value(
                &load_carrier(memory.shared_memory(), pointer),
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        AlgebraicTermNode::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_binder_variables(
                condition,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            collect_binder_variables_in_algebraic_term(
                then_term,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            collect_binder_variables_in_algebraic_term(
                else_term,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_binder_variables_in_algebraic_term(
                scrutinee,
                integer_variables,
                bitvector_variables,
                integer_seen,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    if crate::instrumentation::checked_collection_exhausted() {
                        return;
                    }
                    collect_binder_variables_in_algebraic_value(
                        binding,
                        integer_variables,
                        bitvector_variables,
                        integer_seen,
                    );
                }
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_algebraic_term(
                    &arm.body,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                if crate::instrumentation::checked_collection_exhausted() {
                    return;
                }
                collect_binder_variables_in_pure_argument(
                    argument,
                    integer_variables,
                    bitvector_variables,
                    integer_seen,
                );
            }
        }
    }
}

fn collect_binder_variables_in_algebraic_value(
    value: &AlgebraicValue,
    integer_variables: &mut BTreeSet<Variable>,
    bitvector_variables: &mut BTreeSet<Variable>,
    integer_seen: &mut SeenTerms,
) {
    if checked_collection_checkpoint() {
        return;
    }
    match value {
        AlgebraicValue::Program(value) => collect_binder_variables_in_program_value(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        AlgebraicValue::Integer(value) => collect_integer_binder_variables_seen(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
        AlgebraicValue::Algebraic(value) => collect_binder_variables_in_algebraic_term(
            value,
            integer_variables,
            bitvector_variables,
            integer_seen,
        ),
    }
}

pub(in crate::kernel) fn collect_pointer_offset_bitvector_variables(
    offset: &AddressOffset,
    variables: &mut BTreeSet<Variable>,
) {
    match offset {
        AddressOffset::Constant(_) => {}
        AddressOffset::Variable(variable) => {
            if collecting_connection_variables() || COORDINATE_VARIABLES.with(std::cell::Cell::get)
            {
                variables.insert(*variable);
            }
        }
        AddressOffset::Add(left, right) => {
            collect_pointer_offset_bitvector_variables(left, variables);
            collect_pointer_offset_bitvector_variables(right, variables);
        }
        AddressOffset::Int32Scaled { value, .. } | AddressOffset::Int64Scaled { value, .. } => {
            collect_machine_bitvector_variables(value, variables);
        }
    }
}

pub(in crate::kernel) fn collect_pointer_bitvector_variables(
    pointer: &Address,
    variables: &mut BTreeSet<Variable>,
) {
    collect_address_base_bitvector_variables(&pointer.base, variables);
    collect_pointer_offset_bitvector_variables(&pointer.offset, variables);
}

fn collect_address_base_bitvector_variables(
    block: &AddressBase,
    variables: &mut BTreeSet<Variable>,
) {
    CONNECTION_BLOCKS.with(|blocks| {
        // ExternalArgument is the shared address arena of all formal array
        // parameters. Their offset variables identify the actual objects;
        // sharing that arena must not connect otherwise unrelated arrays.
        // Null is another shared constant: unrelated non-null assertions must
        // not connect all their objects through the null pointer.
        if let Some(blocks) = blocks.borrow_mut().as_mut()
            && !matches!(
                *block,
                AddressBase::ExternalArgument
                    | AddressBase::Symbolic(_)
                    | AddressBase::FunctionSymbolic(_)
                    | AddressBase::ExternalObject(_)
            )
            && !matches!(block, AddressBase::Concrete(name) if name == "null")
        {
            blocks.insert(block.clone());
        }
    });
    match block {
        AddressBase::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_capture_variables_in_pure_argument(
                    argument,
                    variables,
                    &mut SeenTerms::default(),
                );
            }
        }
        AddressBase::Symbolic(variable)
        | AddressBase::FunctionSymbolic(variable)
        | AddressBase::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        // A pointer read has no variable of its own, but it is the value at
        // the address it was read from, so it depends on that address's
        // variables, as a load term depends on its address's.
        AddressBase::LoadedPointer(identity) => {
            if let Some((_, address)) = crate::kernel::eval::registered_pointer_load(*identity) {
                collect_pointer_bitvector_variables(&address, variables);
            }
        }
        AddressBase::ContractResult
        | AddressBase::ContractException
        | AddressBase::AggregateReturn { .. }
        | AddressBase::StaticObject { .. }
        | AddressBase::AutomaticLocal { .. }
        | AddressBase::ReferenceCarrier { .. }
        | AddressBase::Concrete(_)
        | AddressBase::StringLiteral { .. }
        | AddressBase::Function(_)
        | AddressBase::ExternalArgument
        | AddressBase::Heap(_)
        | AddressBase::Temporary(_) => {}
    }
}

#[cfg(test)]
thread_local! {
    /// How many concrete and union cells, and how many run slots, variable
    /// collection has visited on this thread: the scaling regressions'
    /// measure of a collection, whose visits are not all charged.
    static CELLS_COLLECTED: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// `operation`'s result and how many cells and run slots variable
/// collection visited while it ran.
#[cfg(test)]
pub(crate) fn count_cells_collected<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    let before = CELLS_COLLECTED.with(std::cell::Cell::get);
    let result = operation();
    let after = CELLS_COLLECTED.with(std::cell::Cell::get);
    (result, after - before)
}

/// The variables a run's cells mention.
///
/// Each slot mentions its pointer's variables and its value's: the value is
/// the slot's load variable, which also mentions the memory and pointer it
/// names. Where [`run_shape_representatives`] finds every slot named at one
/// memory, the slots of one spelling shape mention the same variables except
/// their own load variables, and a representative slot per shape stands for
/// the rest. The load variables of the other slots are left out: they are in
/// the reserved load range no fresh-variable source allocates from, so no
/// caller that avoids what a memory mentions can collide with one, and every
/// term that mentions one of them also mentions the memory and pointer it
/// names, so a caller relating two terms by shared variables still meets
/// them through the variables every slot has. Where the slots have no such
/// shared variable — a run over a block no variable names — or are named at
/// different memories, every slot is visited, except in a symbolic
/// static-storage run, whose slots are never visited to collect its
/// variables ([`symbolic_storage_run_shared_variables`]).
///
/// [`run_shape_representatives`]: crate::kernel::reasoning::memory_resolution::run_shape_representatives
fn collect_cell_run_bitvector_variables(
    run: &crate::kernel::primitives::CellRun,
    variables: &mut BTreeSet<Variable>,
) {
    match run_representative_variables(run) {
        Some(shared) => variables.extend(shared),
        None => {
            for index in run.live_indexes() {
                collect_run_slot_bitvector_variables(run, index, variables);
            }
        }
    }
}

/// The variables of one slot of a run: its pointer's and its value's.
fn collect_run_slot_bitvector_variables(
    run: &crate::kernel::primitives::CellRun,
    index: u32,
    variables: &mut BTreeSet<Variable>,
) {
    #[cfg(test)]
    CELLS_COLLECTED.with(|visited| visited.set(visited.get() + 1));
    collect_pointer_bitvector_variables(&run.slot_pointer(index), variables);
    collect_program_value_bitvector_variables(&run.value(index), variables);
}

/// The variables a run's representative slots mention, when they stand for
/// the whole run (see [`collect_cell_run_bitvector_variables`]); `None` when
/// every slot has to be visited.
fn run_representative_variables(
    run: &crate::kernel::primitives::CellRun,
) -> Option<BTreeSet<Variable>> {
    match run.value_mode() {
        crate::kernel::primitives::RunValueMode::Constant(value) => {
            return Some(constant_run_variables(run, value));
        }
        crate::kernel::primitives::RunValueMode::Copy { source_base } => {
            let mut shared = symbolic_storage_run_shared_variables(run);
            collect_pointer_bitvector_variables(source_base, &mut shared);
            return Some(shared);
        }
        crate::kernel::primitives::RunValueMode::Load => {}
    }
    let representatives =
        crate::kernel::reasoning::memory_resolution::run_shape_representatives(run)?;
    let mut shared = BTreeSet::new();
    for index in &representatives {
        collect_run_slot_bitvector_variables(run, *index, &mut shared);
    }
    shared
        .iter()
        .any(|variable| !crate::kernel::is_load_variable(variable))
        .then_some(shared)
}

/// The variables every slot of a symbolic static-storage run mentions
/// besides its own load variable, found without naming any slot.
///
/// Slot `i` holds the entry value of storage the function knows nothing
/// about ([`crate::kernel::eval::symbolic_storage_cell_value`]): its own load
/// of the slot's pointer in the run's source, which holds only the storage's
/// block, spelled as a load variable (or a symbolic pointer named by one).
/// What such a value mentions is that load variable and, through it, the
/// source and the slot's pointer; every slot's pointer is the base plus a
/// constant, so the base's variables and the source's are what every slot
/// shares. They are returned here, and the slots' own load variables are
/// left out, for the reasons [`collect_cell_run_bitvector_variables`] gives
/// for a run's non-representative slots: they are in the reserved load
/// range, so no caller avoiding what a memory mentions can collide with one,
/// and a substitution of one finds its slot by the registry
/// (`run_slot_named_by_load_variable`), not by these variables. Unlike a
/// representative-backed run, a global array's slots often share no variable
/// at all, so a premise search that grows its premises by shared variables
/// does not reach this memory from a fact about one element; such a search
/// only chooses premises, so it can miss a proof but not admit one. Naming each
/// slot to collect its variable instead made every collection over a
/// million-element global array mint a million load identities, exhausting
/// the load registry at function entry, and cost the array's length per
/// collection. A slot's identity is minted when the slot is first read.
fn symbolic_storage_run_shared_variables(
    run: &crate::kernel::primitives::CellRun,
) -> BTreeSet<Variable> {
    crate::instrumentation::record_deterministic_work(1);
    let mut shared = BTreeSet::new();
    collect_pointer_bitvector_variables(run.base(), &mut shared);
    collect_shared_memory_bitvector_variables(run.source(), &mut shared);
    shared
}

/// The variables every slot of a constant run mentions: its base pointer's
/// and its one value's. Each slot's pointer is the base plus a constant and
/// each holds that value, so these are exactly the variables of every slot,
/// found without visiting one.
fn constant_run_variables(
    run: &crate::kernel::primitives::CellRun,
    value: &ProgramValue,
) -> BTreeSet<Variable> {
    crate::instrumentation::record_deterministic_work(1);
    let mut shared = BTreeSet::new();
    collect_pointer_bitvector_variables(run.base(), &mut shared);
    collect_program_value_bitvector_variables(value, &mut shared);
    shared
}

/// How many of a state's entries (blocks, concrete cells, runs, union
/// cells) mention each variable. Persistent, so a state's counts share
/// every unchanged node with its derivation base's.
type VariableCounts = crate::persistent::PersistentMap<Variable, u32>;

thread_local! {
    /// The variables each interned state mentions, by arena identity, for
    /// the whole verification session, as counts per entry.
    ///
    /// A state's cells hold loads of earlier states, directly or
    /// through load variables, so the states a collection reaches are a
    /// DAG, and a later state holds every cell of the history before it.
    /// Walking each reached state whole per collection made a collection
    /// cost the whole memory, and walking the DAG as a tree cost every path
    /// to each state. Here a state's counts are its derivation base's
    /// adjusted by the entries the two differ on, which the persistent maps'
    /// diffs visit without the shared rest, so a store or an allocation costs
    /// what it changed, and each state is counted once per session.
    ///
    /// The answer is a function of the state's content and of the load
    /// registry, which never renames or drops a load variable within a
    /// session, and arena identities are never reused, so remembered counts
    /// cannot go stale. [`clear_shared_memory_variables`] empties the table
    /// at every outermost [`crate::kernel::VerificationSession`] entry, which
    /// also clears the registry and starts a fresh arena.
    static SHARED_MEMORY_VARIABLES: std::cell::RefCell<
        std::collections::HashMap<(u32, u32), VariableCounts>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
    // Pointer-read projections share heap metadata even when their selected
    // cells differ. Retain the root, so an address cannot be reused for a hit.
    static HEAP_VARIABLES: std::cell::RefCell<Option<(std::sync::Arc<crate::kernel::primitives::HeapMemory>, VariableCounts)>> = const { std::cell::RefCell::new(None) };
}

/// Forgets every state's remembered variables; see
/// [`SHARED_MEMORY_VARIABLES`].
pub(in crate::kernel) fn clear_shared_memory_variables() {
    SHARED_MEMORY_VARIABLES.with(|table| table.borrow_mut().clear());
    HEAP_VARIABLES.with(|table| *table.borrow_mut() = None);
}

fn remembered_memory_variables(memory: &SharedMemory) -> Option<VariableCounts> {
    SHARED_MEMORY_VARIABLES.with(|table| table.borrow().get(&memory.arena_id()).cloned())
}

/// Read an already prepared state's variable index without walking its memory.
/// Missing metadata leaves the caller on its existing checked path.
pub(in crate::kernel) fn indexed_memory_contains_variable(
    memory: &SharedMemory,
    variable: Variable,
) -> Option<bool> {
    crate::instrumentation::record_deterministic_work(1);
    Some(remembered_memory_variables(memory)?.contains_key(&variable))
}

/// Establish the input state's index once, before individual C steps.
pub(in crate::kernel) fn prepare_memory_variable_index(memory: &SymbolicMemory) {
    let shared = crate::kernel::intern_memory_ref(memory);
    shared_memory_variable_counts(&shared, WholeCount::Charged);
}

/// Advance an established index by the exact memory delta. Unindexed
/// executions remain lazy; an indexed execution never leaves a later call
/// to pay for all preceding stores.
pub(in crate::kernel) fn advance_memory_variable_index(base: &SharedMemory, result: &SharedMemory) {
    if remembered_memory_variables(result).is_some() {
        return;
    }
    if let Some(counts) = remembered_memory_variables(base) {
        let counts = counts_from_base(counts, base.memory(), result.memory());
        SHARED_MEMORY_VARIABLES.with(|table| {
            table.borrow_mut().insert(result.arena_id(), counts);
        });
    }
}

/// [`collect_memory_bitvector_variables`] of an interned state, counted
/// once per verification session from its derivation base's counts. Counting
/// charges one unit per entry and per derivation step it visits; a state
/// already counted is an indexed lookup plus the variables it hands back.
pub(in crate::kernel) fn collect_shared_memory_bitvector_variables(
    memory: &SharedMemory,
    variables: &mut BTreeSet<Variable>,
) {
    if COLLECTING_HAVOC_RANGES.with(std::cell::Cell::get)
        && FRAME_STATES.with(|seen| seen.borrow_mut().insert(memory.arena_id()))
    {
        // The ranges a call or loop wrote to reach this state: a fact
        // about one of their bounds is what frames a load across the edge.
        let mut current = memory.clone();
        for _ in 0..HAVOC_RANGE_HOPS {
            let Some(derivation) = current.derivation() else {
                break;
            };
            crate::instrumentation::record_deterministic_work(1);
            match derivation.as_ref() {
                MemoryDerivation::Store { pointer, .. } => {
                    collect_pointer_bitvector_variables(pointer, variables);
                }
                MemoryDerivation::CallHavoc { mutable_ranges, .. } => {
                    for range in mutable_ranges {
                        collect_memory_range_bitvector_variables(range, variables);
                    }
                }
                MemoryDerivation::LoopHavoc {
                    mutable_ranges: Some(mutable_ranges),
                    ..
                } => {
                    for range in mutable_ranges {
                        collect_memory_range_bitvector_variables(range, variables);
                    }
                }
                _ => {}
            }
            current = derivation.base().clone();
        }
    }
    if collecting_connection_variables() || defer_condition_state() {
        return;
    }

    extend_with_state_variables(memory, WholeCount::Charged, variables);
}

/// The states a fact set already reserves, while it reserves one more
/// fact's variables (`proposition_variables_reserving`), and the states
/// that fact's collection met.
struct StateReservation {
    reserved: crate::persistent::PersistentSet<(u32, u32)>,
    met: BTreeSet<(u32, u32)>,
    /// The states whose bound variables the fact set already reserves,
    /// and those this fact's collection walked for them.
    bound_reserved: crate::persistent::PersistentSet<(u32, u32)>,
    bound_walked: BTreeSet<(u32, u32)>,
}

/// The interned states whose variables a fact set already reserves: for
/// their free variables (`variables`), and separately for their bound
/// variables (`bound`). A state reached only through another's loads is
/// counted for its free variables without its bound variables being walked,
/// so the two are kept apart.
#[derive(Clone, Default)]
pub(in crate::kernel) struct ReservedStates {
    variables: crate::persistent::PersistentSet<(u32, u32)>,
    bound: crate::persistent::PersistentSet<(u32, u32)>,
}

/// Whether the bound-variable walk of the interned state `identity` can
/// be skipped while a fact set reserves a fact's variables
/// (`proposition_variables_reserving`): the set already reserves its bound
/// variables, or this fact's collection already walked it. Marks it walked
/// otherwise. Outside a reservation nothing is skipped.
pub(in crate::kernel) fn bound_state_already_reserved(identity: (u32, u32)) -> bool {
    STATE_RESERVATION.with(|cell| {
        cell.borrow_mut().as_mut().is_some_and(|reservation| {
            reservation.bound_reserved.contains(&identity)
                || !reservation.bound_walked.insert(identity)
        })
    })
}

thread_local! {
    /// Set while `proposition_mentions_load_variable` collects: a state
    /// contributes at most one load variable, which is all that question
    /// reads of it.
    static LOAD_PRESENCE_ONLY: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Collects `proposition`'s variables as `collect_proposition_bitvector_variables`
/// does, except that each interned state contributes at most one of its
/// load variables: the result names a load variable exactly when the whole
/// collection does.
pub(in crate::kernel) fn collect_proposition_variables_for_load_presence(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            LOAD_PRESENCE_ONLY.with(|flag| flag.set(self.0));
        }
    }
    let _restore = Restore(LOAD_PRESENCE_ONLY.with(|flag| flag.replace(true)));
    collect_proposition_bitvector_variables(proposition, variables);
}

thread_local! {
    static STATE_RESERVATION: std::cell::RefCell<Option<StateReservation>> =
        const { std::cell::RefCell::new(None) };
}

/// How far back a state's derivation is followed for one whose
/// variables are already reserved.
const RESERVED_STATE_HOPS: usize = 64;

/// Adds `memory`'s variables, as its remembered counts list them. While a
/// fact set reserves a fact's variables, a state it already reserves adds
/// none, and one derived from such a state adds the variables of the
/// entries the two differ on: every variable of `memory` is one of those or
/// one of the reserved state's, and every one of those is `memory`'s, so
/// the reserved variables come out as they would from its whole counts.
fn extend_with_state_variables(
    memory: &SharedMemory,
    whole: WholeCount,
    variables: &mut BTreeSet<Variable>,
) {
    if LOAD_PRESENCE_ONLY.with(std::cell::Cell::get) {
        // Whether the state names a load variable is whether its counts
        // hold one: the first one stands for them all.
        let counts = shared_memory_variable_counts(memory, whole);
        variables.extend(
            counts
                .get_greater_than(&Variable(
                    crate::kernel::eval::LOAD_VARIABLE_RANGE.start - 1,
                ))
                .map(|(variable, _)| *variable)
                .filter(crate::kernel::is_load_variable),
        );
        return;
    }
    let Some(mut reservation) = STATE_RESERVATION.with(|cell| cell.borrow_mut().take()) else {
        variables.extend(shared_memory_variable_counts(memory, whole).keys().copied());
        return;
    };
    let id = memory.arena_id();
    let known = |reservation: &StateReservation, id: &(u32, u32)| {
        reservation.reserved.contains(id) || reservation.met.contains(id)
    };
    if !known(&reservation, &id) {
        let mut current = memory.clone();
        let mut reserved_base = None;
        for _ in 0..RESERVED_STATE_HOPS {
            let Some(derivation) = current.derivation() else {
                break;
            };
            let base = derivation.base().clone();
            if known(&reservation, &base.arena_id()) {
                reserved_base = Some(base);
                break;
            }
            current = base;
        }
        reservation.met.insert(id);
        match reserved_base {
            Some(base) => {
                // The entries' own loads may reach further states; the
                // reservation stays in force for those.
                STATE_RESERVATION.with(|cell| *cell.borrow_mut() = Some(reservation));
                variables.extend(variables_entering(base.memory(), memory.memory()));
                reservation = STATE_RESERVATION
                    .with(|cell| cell.borrow_mut().take())
                    .expect("the reservation survives its own collection");
            }
            // Counting is shared by the whole session, so it runs without
            // the reservation.
            None => variables.extend(shared_memory_variable_counts(memory, whole).keys().copied()),
        }
    }
    STATE_RESERVATION.with(|cell| *cell.borrow_mut() = Some(reservation));
}

/// The nearest state `memory` derives from, within
/// `RESERVED_STATE_HOPS` steps, whose bound variables the fact set being
/// built already reserves or this fact's collection already walked; `None`
/// outside a reservation. Its bound variables together with those of the
/// entries `memory` changes since include all of `memory`'s.
pub(in crate::kernel) fn bound_reserved_base(
    memory: &crate::kernel::primitives::SharedMemory,
) -> Option<crate::kernel::primitives::SharedMemory> {
    STATE_RESERVATION.with(|cell| {
        let reservation = cell.borrow();
        let reservation = reservation.as_ref()?;
        let mut current = memory.clone();
        for _ in 0..RESERVED_STATE_HOPS {
            let base = current.derivation()?.base().clone();
            let id = base.arena_id();
            if reservation.bound_reserved.contains(&id) || reservation.bound_walked.contains(&id) {
                return Some(base);
            }
            current = base;
        }
        None
    })
}

/// The variables of every entry `memory` holds that `base` does not hold
/// the same, by the diffs `counts_from_base` reads: together with `base`'s
/// variables they include all of `memory`'s, and each is one of `memory`'s.
fn variables_entering(base: &SymbolicMemory, memory: &SymbolicMemory) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    for change in base.blocks.diff(&memory.blocks) {
        let block = change.key();
        if let Some(contents) = memory.blocks.get(block) {
            variables.extend(block_variables(block, contents));
        }
    }
    for (before, after) in [
        (
            &base.heap.uninitialized_objects,
            &memory.heap.uninitialized_objects,
        ),
        (
            base.heap.initialized.as_map(),
            memory.heap.initialized.as_map(),
        ),
    ] {
        for change in before.diff(after) {
            let pointer = change.key();
            if after.contains_key(pointer) {
                variables.extend(object_address_variables(pointer));
            }
        }
    }
    let before = base.heap.initialized.partial_map();
    let after = memory.heap.initialized.partial_map();
    for change in before.diff(after) {
        let pointer = change.key();
        if let Some(byte) = after.get(pointer) {
            variables.extend(partial_byte_variables(pointer, byte.value.as_ref()));
        }
    }
    for change in base.cells.concrete().diff(memory.cells.concrete()) {
        let pointer = change.key();
        if let Some(value) = memory.cells.concrete().get(pointer) {
            variables.extend(stored_cell_variables(pointer, value));
        }
    }
    for (_, after) in base.cells.run_diff(&memory.cells) {
        let Some(run) = after else {
            continue;
        };
        match run_representative_variables(run) {
            Some(shared) => variables.extend(shared),
            None => {
                for index in run.live_indexes() {
                    variables.extend(run_slot_variables(run, index));
                }
            }
        }
    }
    for change in base.union_cells.diff(&memory.union_cells) {
        let key = change.key();
        if let Some(value) = memory.union_cells.get(key) {
            variables.extend(cell_variables(&key.0, value.native()));
        }
    }
    variables
}

/// `proposition_variables(proposition)` for a fact set whose reserved
/// variables already include every variable of the states `reserved`
/// names: the variables to reserve beyond those, with `reserved` extended
/// by the states the collection met, whose variables the reserved ones
/// then include.
pub(in crate::kernel) fn proposition_variables_reserving(
    proposition: &Proposition,
    reserved: &mut ReservedStates,
) -> BTreeSet<Variable> {
    struct Restore(Option<StateReservation>);
    impl Drop for Restore {
        fn drop(&mut self) {
            STATE_RESERVATION.with(|cell| *cell.borrow_mut() = self.0.take());
        }
    }
    let previous = STATE_RESERVATION.with(|cell| {
        cell.borrow_mut().replace(StateReservation {
            reserved: reserved.variables.clone(),
            met: BTreeSet::new(),
            bound_reserved: reserved.bound.clone(),
            bound_walked: BTreeSet::new(),
        })
    });
    let restore = Restore(previous);
    let variables = crate::kernel::proposition_variables(proposition);
    if let Some(reservation) = STATE_RESERVATION.with(|cell| cell.borrow_mut().take()) {
        for retained_state in reservation.met {
            reserved.variables = reserved.variables.with_value(retained_state);
        }
        for retained_state in reservation.bound_walked {
            reserved.bound = reserved.bound.with_value(retained_state);
        }
    }
    drop(restore);
    variables
}

/// Whether counting a state of the chain whole is charged; see
/// [`collect_memory_bitvector_variables`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum WholeCount {
    Charged,
    Uncharged,
}

fn shared_memory_variable_counts(memory: &SharedMemory, whole: WholeCount) -> VariableCounts {
    if let Some(counts) = remembered_memory_variables(memory) {
        return counts;
    }
    // The uncounted derivation ancestors, nearest first, up to one already
    // counted or with no recorded base. The walk is cut at the state's own
    // size: past that, counting the state whole costs less than counting
    // its history.
    let limit = memory_entry_count(memory.memory());
    let mut chain = vec![memory.clone()];
    let mut counted_base = None;
    while chain.len() <= limit {
        let Some(derivation) = chain
            .last()
            .expect("the chain starts nonempty")
            .derivation()
        else {
            break;
        };
        let base = derivation.base().clone();
        crate::instrumentation::record_deterministic_work(1);
        if let Some(counts) = remembered_memory_variables(&base) {
            counted_base = Some((base, counts));
            break;
        }
        chain.push(base);
    }
    if counted_base.is_none() && chain.len() > limit {
        // Too long a history: count this state alone, whole.
        chain.truncate(1);
    }
    // Oldest first: each state is counted from the one before it.
    let mut previous = counted_base;
    for retained_state in chain.into_iter().rev() {
        let counts = match &previous {
            Some((base, counts)) => {
                counts_from_base(counts.clone(), base.memory(), retained_state.memory())
            }
            None => counts_whole(retained_state.memory(), whole),
        };
        SHARED_MEMORY_VARIABLES.with(|table| {
            table
                .borrow_mut()
                .insert(retained_state.arena_id(), counts.clone());
        });
        previous = Some((retained_state, counts));
    }
    previous.expect("the chain counts at least the state").1
}

fn memory_entry_count(memory: &SymbolicMemory) -> usize {
    memory.blocks.len()
        + memory.cells.representation_len()
        + memory.union_cells.len()
        + memory.heap.uninitialized_objects.len()
        + memory.heap.initialized.as_map().len()
        + memory.heap.initialized.partial_map().len()
}

fn add_counts(counts: &mut VariableCounts, mentioned: BTreeSet<Variable>, sign: i64) {
    for variable in mentioned {
        let held = i64::from(counts.get(&variable).copied().unwrap_or(0));
        let count = held + sign;
        debug_assert!(
            count >= 0,
            "an entry's variables are counted before removal"
        );
        if count <= 0 {
            counts.remove(&variable);
        } else {
            counts.insert(
                variable,
                u32::try_from(count).expect("entry counts fit in u32"),
            );
        }
    }
}

fn block_variables(block: &AddressBase, contents: &MemoryBlock) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    match block {
        AddressBase::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_capture_variables_in_pure_argument(
                    argument,
                    &mut variables,
                    &mut SeenTerms::default(),
                );
            }
        }
        AddressBase::Symbolic(variable)
        | AddressBase::FunctionSymbolic(variable)
        | AddressBase::ExternalObject(variable) => {
            variables.insert(*variable);
        }
        AddressBase::ContractResult
        | AddressBase::ContractException
        | AddressBase::AggregateReturn { .. }
        | AddressBase::StaticObject { .. }
        | AddressBase::AutomaticLocal { .. }
        | AddressBase::ReferenceCarrier { .. }
        | AddressBase::Concrete(_)
        | AddressBase::StringLiteral { .. }
        | AddressBase::Function(_)
        | AddressBase::ExternalArgument
        | AddressBase::LoadedPointer(_)
        | AddressBase::Heap(_)
        | AddressBase::Temporary(_) => {}
    }
    // A memory-havoc marker spells the identity it was minted with in its
    // block name instead of carrying it in a term, so a scan of the
    // state's terms alone does not see it. Reserving it here is what lets
    // every caller that must avoid what a state already mentions -- a
    // branch join's abstraction, a loop head's stream, a constructor
    // witness -- see it without harvesting block names by hand.
    for prefix in ["havoc:", "call-havoc:"] {
        if let Some(index) = block
            .strip_prefix(prefix)
            .and_then(|index| index.parse::<u64>().ok())
        {
            variables.insert(Variable(index));
        }
    }
    collect_bitvector_variables(contents.size(), &mut variables);
    variables
}

fn object_address_variables(pointer: &Address) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_pointer_bitvector_variables(pointer, &mut variables);
    variables
}

fn partial_byte_variables(pointer: &Address, value: Option<&ProgramValue>) -> BTreeSet<Variable> {
    match value {
        Some(value) => cell_variables(pointer, value),
        None => object_address_variables(pointer),
    }
}

fn add_partial_byte_changes(
    before: &super::super::primitives::InitializedBytes,
    after: &super::super::primitives::InitializedBytes,
    counts: &mut VariableCounts,
) {
    let before = before.partial_map();
    let after = after.partial_map();
    for change in before.diff(after) {
        crate::instrumentation::record_deterministic_work(1);
        let pointer = change.key();
        if let Some(byte) = before.get(pointer) {
            add_counts(
                counts,
                partial_byte_variables(pointer, byte.value.as_ref()),
                -1,
            );
        }
        if let Some(byte) = after.get(pointer) {
            add_counts(
                counts,
                partial_byte_variables(pointer, byte.value.as_ref()),
                1,
            );
        }
    }
}

fn cell_variables(pointer: &Address, value: &ProgramValue) -> BTreeSet<Variable> {
    #[cfg(test)]
    CELLS_COLLECTED.with(|visited| visited.set(visited.get() + 1));
    let mut variables = BTreeSet::new();
    collect_pointer_bitvector_variables(pointer, &mut variables);
    collect_program_value_bitvector_variables(value, &mut variables);
    variables
}

fn stored_cell_variables(pointer: &Address, value: &StoredMemoryValue) -> BTreeSet<Variable> {
    if !value.is_retained_word() {
        return cell_variables(pointer, value.native());
    }
    #[cfg(test)]
    CELLS_COLLECTED.with(|visited| visited.set(visited.get() + 1));
    let mut variables = BTreeSet::new();
    collect_pointer_bitvector_variables(pointer, &mut variables);
    collect_expression_value_bitvector_variables(value.value(), &mut variables);
    variables
}

/// Counts a run's variables in or out: as one entry when its
/// representatives stand for it, and otherwise as one entry per live slot.
/// Either way the variables counted are exactly the run's
/// ([`collect_cell_run_bitvector_variables`]); per slot, a store into the run
/// changes the counts by the slots it changes rather than by the whole run.
fn add_run_counts(
    counts: &mut VariableCounts,
    run: &crate::kernel::primitives::CellRun,
    sign: i64,
) {
    match run_representative_variables(run) {
        Some(shared) => add_counts(counts, shared, sign),
        None => {
            for index in run.live_indexes() {
                crate::instrumentation::record_deterministic_work(1);
                add_counts(counts, run_slot_variables(run, index), sign);
            }
        }
    }
}

fn run_slot_variables(run: &crate::kernel::primitives::CellRun, index: u32) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    collect_run_slot_bitvector_variables(run, index, &mut variables);
    variables
}

/// A run held on both sides of a diff with other holes, counted per slot on
/// both: only the slots whose liveness differs change the counts. `false`
/// when either side is counted as one entry, and the caller counts the two
/// sides whole.
fn adjust_run_counts_by_changed_slots(
    counts: &mut VariableCounts,
    before: &crate::kernel::primitives::CellRun,
    after: &crate::kernel::primitives::CellRun,
) -> bool {
    if !before.same_slots_as(after)
        || run_representative_variables(before).is_some()
        || run_representative_variables(after).is_some()
    {
        return false;
    }
    let changed = before.holes().symmetric_difference(after.holes());
    crate::instrumentation::record_deterministic_work(changed.interval_count());
    for index in changed.indexes() {
        crate::instrumentation::record_deterministic_work(1);
        // The two runs have the same slots holding the same values, so a
        // slot's variables are the same on both sides.
        let sign = if after.holes().contains(index) { -1 } else { 1 };
        add_counts(counts, run_slot_variables(before, index), sign);
    }
    true
}

/// A state's counts from all of its entries; one unit per entry unless
/// `whole` is [`WholeCount::Uncharged`].
fn heap_variable_counts(
    heap: &std::sync::Arc<crate::kernel::primitives::HeapMemory>,
    whole: WholeCount,
) -> VariableCounts {
    let previous = HEAP_VARIABLES.with(|table| table.borrow().clone());
    let counts = if let Some((base, mut counts)) = previous {
        if std::sync::Arc::ptr_eq(&base, heap) {
            return counts;
        }
        for (before, after) in [
            (&base.uninitialized_objects, &heap.uninitialized_objects),
            (base.initialized.as_map(), heap.initialized.as_map()),
        ] {
            for change in before.diff(after) {
                crate::instrumentation::record_deterministic_work(1);
                let pointer = change.key();
                if before.contains_key(pointer) {
                    add_counts(&mut counts, object_address_variables(pointer), -1);
                }
                if after.contains_key(pointer) {
                    add_counts(&mut counts, object_address_variables(pointer), 1);
                }
            }
        }
        add_partial_byte_changes(&base.initialized, &heap.initialized, &mut counts);
        counts
    } else {
        if whole == WholeCount::Charged {
            crate::instrumentation::record_deterministic_work(
                heap.uninitialized_objects.len()
                    + heap.initialized.as_map().len()
                    + heap.initialized.partial_map().len(),
            );
        }
        let mut counts = VariableCounts::default();
        for pointer in heap
            .uninitialized_objects
            .keys()
            .chain(heap.initialized.as_map().keys())
        {
            add_counts(&mut counts, object_address_variables(pointer), 1);
        }
        for (pointer, byte) in heap.initialized.partial_map().iter() {
            add_counts(
                &mut counts,
                partial_byte_variables(pointer, byte.value.as_ref()),
                1,
            );
        }
        counts
    };
    HEAP_VARIABLES.with(|table| *table.borrow_mut() = Some((heap.clone(), counts.clone())));
    counts
}

fn counts_whole(memory: &SymbolicMemory, whole: WholeCount) -> VariableCounts {
    if whole == WholeCount::Charged {
        crate::instrumentation::record_deterministic_work(
            memory.blocks.len() + memory.cells.representation_len() + memory.union_cells.len(),
        );
    }
    // Start from the retained heap counts, rather than enumerating their
    // variables to combine them with each selected read projection.
    let mut counts = heap_variable_counts(&memory.heap, whole);
    for (block, contents) in memory.blocks.iter() {
        add_counts(&mut counts, block_variables(block, contents), 1);
    }
    for (pointer, value) in memory.cells.concrete().iter() {
        add_counts(&mut counts, stored_cell_variables(pointer, value), 1);
    }
    for run in memory.cells.runs() {
        add_run_counts(&mut counts, run, 1);
    }
    for ((pointer, _), value) in memory.union_cells.iter() {
        add_counts(&mut counts, stored_cell_variables(pointer, value), 1);
    }
    counts
}

/// `memory`'s counts from `base`'s: each entry the two differ on leaves with
/// its old variables and arrives with its new ones. The diffs charge one unit
/// per difference.
fn counts_from_base(
    mut counts: VariableCounts,
    base: &SymbolicMemory,
    memory: &SymbolicMemory,
) -> VariableCounts {
    for change in base.blocks.diff(&memory.blocks) {
        let block = change.key();
        if let Some(contents) = base.blocks.get(block) {
            add_counts(&mut counts, block_variables(block, contents), -1);
        }
        if let Some(contents) = memory.blocks.get(block) {
            add_counts(&mut counts, block_variables(block, contents), 1);
        }
    }
    for (before, after) in [
        (
            &base.heap.uninitialized_objects,
            &memory.heap.uninitialized_objects,
        ),
        (
            base.heap.initialized.as_map(),
            memory.heap.initialized.as_map(),
        ),
    ] {
        for change in before.diff(after) {
            let pointer = change.key();
            if before.contains_key(pointer) {
                add_counts(&mut counts, object_address_variables(pointer), -1);
            }
            if after.contains_key(pointer) {
                add_counts(&mut counts, object_address_variables(pointer), 1);
            }
        }
    }
    add_partial_byte_changes(
        &base.heap.initialized,
        &memory.heap.initialized,
        &mut counts,
    );
    for change in base.cells.concrete().diff(memory.cells.concrete()) {
        let pointer = change.key();
        if let Some(value) = base.cells.concrete().get(pointer) {
            add_counts(&mut counts, stored_cell_variables(pointer, value), -1);
        }
        if let Some(value) = memory.cells.concrete().get(pointer) {
            add_counts(&mut counts, stored_cell_variables(pointer, value), 1);
        }
    }
    for (before, after) in base.cells.run_diff(&memory.cells) {
        if let (Some(before), Some(after)) = (before, after)
            && adjust_run_counts_by_changed_slots(&mut counts, before, after)
        {
            continue;
        }
        if let Some(run) = before {
            add_run_counts(&mut counts, run, -1);
        }
        if let Some(run) = after {
            add_run_counts(&mut counts, run, 1);
        }
    }
    for change in base.union_cells.diff(&memory.union_cells) {
        let key = change.key();
        if let Some(value) = base.union_cells.get(key) {
            add_counts(&mut counts, cell_variables(&key.0, value.native()), -1);
        }
        if let Some(value) = memory.union_cells.get(key) {
            add_counts(&mut counts, cell_variables(&key.0, value.native()), 1);
        }
    }
    counts
}

/// An interned state a cell's load reaches is walked through
/// [`collect_shared_memory_bitvector_variables`], once per session.
pub(in crate::kernel) fn collect_memory_bitvector_variables(
    memory: &SymbolicMemory,
    variables: &mut BTreeSet<Variable>,
) {
    if collecting_connection_variables() {
        return;
    }
    if defer_condition_state() {
        return;
    }

    // A live state's memory is the interned storage its last derivation
    // left, so its variables are that state's remembered counts, counted
    // once per session from its derivation base's: the work of what changed,
    // not of every cell and run slot again on every collection. Where its
    // history reaches no counted state, one of its chain is counted
    // whole: that is the walk every collection of it made, uncharged, before
    // the counts were kept, and it stays uncharged; the steps back to a
    // counted state and the entries they changed are charged, as are the
    // states its cells' loads reach.
    if let Some(shared) = crate::kernel::primitives::interned_storage_of(memory) {
        if EXECUTION_CEILING_ONLY.with(std::cell::Cell::get) {
            let counts = shared_memory_variable_counts(&shared, WholeCount::Uncharged);
            variables.extend(
                counts
                    .get_less_than(&Variable(
                        crate::kernel::ExecutionBudget::KERNEL_VARIABLE_CEILING,
                    ))
                    .map(|(variable, _)| *variable),
            );
            return;
        }
        extend_with_state_variables(&shared, WholeCount::Uncharged, variables);
        return;
    }
    collect_memory_bitvector_variables_whole(memory, variables);
}

/// [`collect_memory_bitvector_variables`] by visiting every entry of
/// `memory`, for a state no derivation interned. The counts of
/// [`shared_memory_variable_counts`] are built from the same per-entry
/// collectors, so the two agree on every state.
pub(in crate::kernel) fn collect_memory_bitvector_variables_whole(
    memory: &SymbolicMemory,
    variables: &mut BTreeSet<Variable>,
) {
    if collecting_connection_variables() {
        return;
    }
    if defer_condition_state() {
        return;
    }

    for (block, contents) in memory.blocks.iter() {
        match block {
            AddressBase::PureFunctionApplication(application) => {
                for argument in application.arguments() {
                    collect_capture_variables_in_pure_argument(
                        argument,
                        variables,
                        &mut SeenTerms::default(),
                    );
                }
            }
            AddressBase::Symbolic(variable)
            | AddressBase::FunctionSymbolic(variable)
            | AddressBase::ExternalObject(variable) => {
                variables.insert(*variable);
            }
            AddressBase::ContractResult
            | AddressBase::ContractException
            | AddressBase::AggregateReturn { .. }
            | AddressBase::StaticObject { .. }
            | AddressBase::AutomaticLocal { .. }
            | AddressBase::ReferenceCarrier { .. }
            | AddressBase::Concrete(_)
            | AddressBase::StringLiteral { .. }
            | AddressBase::Function(_)
            | AddressBase::ExternalArgument
            | AddressBase::LoadedPointer(_)
            | AddressBase::Heap(_)
            | AddressBase::Temporary(_) => {}
        }
        // A memory-havoc marker spells the identity it was minted with in its
        // block name instead of carrying it in a term, so a scan of the
        // state's terms alone does not see it. Reserving it here is what lets
        // every caller that must avoid what a state already mentions -- a
        // branch join's abstraction, a loop head's stream, a constructor
        // witness -- see it without harvesting block names by hand.
        for prefix in ["havoc:", "call-havoc:"] {
            if let Some(index) = block
                .strip_prefix(prefix)
                .and_then(|index| index.parse::<u64>().ok())
            {
                variables.insert(Variable(index));
            }
        }
        collect_bitvector_variables(contents.size(), variables);
    }
    for pointer in memory
        .heap
        .uninitialized_objects
        .keys()
        .chain(memory.heap.initialized.as_map().keys())
    {
        collect_pointer_bitvector_variables(pointer, variables);
    }
    for (pointer, byte) in memory.heap.initialized.partial_map().iter() {
        collect_pointer_bitvector_variables(pointer, variables);
        if let Some(value) = &byte.value {
            collect_program_value_bitvector_variables(value, variables);
        }
    }
    for (pointer, value) in memory.cells.concrete().iter() {
        #[cfg(test)]
        CELLS_COLLECTED.with(|visited| visited.set(visited.get() + 1));
        collect_pointer_bitvector_variables(pointer, variables);
        collect_program_value_bitvector_variables(value.native(), variables);
    }
    for run in memory.cells.runs() {
        collect_cell_run_bitvector_variables(run, variables);
    }
    for ((pointer, _), value) in memory.union_cells.iter() {
        collect_pointer_bitvector_variables(pointer, variables);
        collect_program_value_bitvector_variables(value.native(), variables);
    }
}

fn collect_expression_value_bitvector_variables(
    value: &ExecutionValue,
    variables: &mut BTreeSet<Variable>,
) {
    if let Some((_, view @ MachineOperandView::Shared(_))) = value.machine() {
        visit_machine_operand_carrier_leaves(view, |leaf| {
            collect_operand_bitvector_variables(leaf, variables)
        });
    } else {
        collect_program_value_bitvector_variables(&value.native(), variables);
    }
}

pub(crate) fn collect_program_value_bitvector_variables(
    value: &ProgramValue,
    variables: &mut BTreeSet<Variable>,
) {
    match value {
        ProgramValue::PointerInteger(record) => {
            collect_program_value_bitvector_variables(&record.numeric, variables);
            collect_program_value_bitvector_variables(
                &ProgramValue::Pointer(*record.pointer.clone()),
                variables,
            );
        }
        ProgramValue::Parameter(term) => {
            collect_algebraic_term_bitvector_variables(term, variables)
        }
        ProgramValue::Void => {}
        ProgramValue::Int8(bits) => collect_bitvector_variables(bits, variables),
        ProgramValue::Bool(bits)
        | ProgramValue::Int16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits)
        | ProgramValue::UInt32(bits)
        | ProgramValue::Int64(bits)
        | ProgramValue::UInt64(bits)
        | ProgramValue::Int128(bits)
        | ProgramValue::UInt128(bits)
        | ProgramValue::Float32(bits)
        | ProgramValue::Float64(bits) => collect_bitvector_variables(bits, variables),
        ProgramValue::Pointer(pointer) => {
            for address in pointer.pointers() {
                collect_pointer_bitvector_variables(address, variables);
            }
        }
    }
}

#[cfg(test)]
mod integer_expression_tests {
    use super::*;

    #[test]
    fn deferred_integer_arithmetic_collects_machine_variables() {
        let variable = Variable(781);
        let expression = SpecIntegerExpression::Negate(Box::new(SpecIntegerExpression::Add(
            Box::new(SpecIntegerExpression::Term(IntegerTerm::Constant(1.into()))),
            Box::new(SpecIntegerExpression::FromMachine(Box::new(
                SpecExpression::Value(ProgramValue::Int32(MachineTerm::Variable(variable))),
            ))),
        )));
        let mut variables = BTreeSet::new();
        collect_spec_integer_variables(&expression, &mut variables);
        assert_eq!(variables, BTreeSet::from([variable]));
        variables.clear();
        let field = AlgebraicValue::Integer(
            IntegerTerm::from_machine(MachineIntegerType::Int32, MachineTerm::Variable(variable))
                .unwrap(),
        );
        collect_algebraic_value_bitvector_variables(&field, &mut variables);
        assert_eq!(variables, BTreeSet::from([variable]));
    }

    #[test]
    fn integer_binder_collection_shared_dag_has_linear_attempts() {
        let mut attempts_by_depth = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let mut expression = IntegerTerm::Variable(Variable(4_000_000 + depth as u64));
            for _ in 0..depth {
                let child: SharedIntegerTerm = expression.into();
                expression = IntegerTerm::Add(child.clone(), child);
            }

            let mut integer_variables = BTreeSet::new();
            let mut bitvector_variables = BTreeSet::new();
            let attempts = {
                let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
                collect_integer_binder_variables(
                    &expression,
                    &mut integer_variables,
                    &mut bitvector_variables,
                );
                crate::instrumentation::checked_collection_attempts()
            };
            assert!(integer_variables.is_empty());
            assert!(bitvector_variables.is_empty());
            attempts_by_depth.push(attempts);
        }

        for pair in attempts_by_depth.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "shared Integer DAG collector attempts grew superlinearly: {attempts_by_depth:?}"
            );
        }
    }
}

#[cfg(test)]
mod heap_variable_projection_tests {
    use super::*;

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/reasoning/variable_collection/heap_variable_projection_tests.rs"
        );
    }
}

#[cfg(test)]
mod spec_walk_oracle_tests;

#[cfg(test)]
mod shared_machine_collector_tests;

#[cfg(test)]
mod shared_read_walker_tests {
    use super::*;

    #[test]
    fn shared_read_integer_carriers_remain_visible_inside_pointer_calls() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address {
            base: AddressBase::PureFunctionApplication(SharedPureApplication::intern(
                "read_address".into(),
                vec![PureFunctionArgument::Integer(
                    IntegerTerm::Variable(Variable(994120)).into(),
                )],
            )),
            offset: AddressOffset::Constant(0),
        };
        let native = MachineTerm::MemoryLoad(
            ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
            Box::new(pointer),
            LoadKind::Int32,
        );
        let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        assert!(matches!(root.node(), KernelTermNode::MemoryLoad { .. }));
        let mut expected = BTreeSet::new();
        collect_bitvector_integer_variables(&native, &mut expected);
        let mut actual = BTreeSet::new();
        let mut seen = SeenTerms::default();
        visit_machine_operand_carrier_leaves(MachineOperandView::Shared(&root), |leaf| {
            collect_operand_integer_variables_seen(leaf, &mut actual, &mut seen);
        });
        assert_eq!(actual, expected);
        assert!(actual.contains(&Variable(994120)));
    }

    #[test]
    fn shared_read_carriers_match_native_addresses_without_export_or_registry() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address {
            base: AddressBase::Symbolic(Variable(994100)),
            offset: AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(994101)), 4),
        };
        let raw = MachineTerm::MemoryLoad(
            ProgramPoint::at(&(intern_memory(SymbolicMemory::new()))),
            Box::new(pointer),
            LoadKind::Int32,
        );
        let leaf = KernelTermImport::default().machine(MachineIntegerType::Int32, &raw);
        let root = KernelTerm::arithmetic_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            [leaf.clone(), leaf],
        )
        .unwrap();
        let native = MachineTerm::Binary {
            format: MachineIntegerType::Int32,
            op: MachineBinaryOp::Add,
            left: Box::new(raw.clone()),
            right: Box::new(raw),
        };
        crate::kernel::eval::clear_load_variable_registry();
        let mut expected = BTreeSet::new();
        collect_bitvector_variables(&native, &mut expected);
        let exports = KernelTermExport::machine_export_count();
        let mut actual = BTreeSet::new();
        let mut reads = 0;
        visit_machine_operand_carrier_leaves(MachineOperandView::Shared(&root), |leaf| {
            reads += usize::from(leaf.read().is_some());
            collect_operand_bitvector_variables(leaf, &mut actual);
        });
        assert_eq!(actual, expected);
        assert!(actual.contains(&Variable(994100)));
        assert!(actual.contains(&Variable(994101)));
        assert_eq!(reads, 1, "a shared read is selected once");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
