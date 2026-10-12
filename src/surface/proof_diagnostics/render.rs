//! A bounded renderer for kernel propositions used in proof failure reports.
//!
//! This deliberately has its own small printer.  `Debug` for a proposition is
//! useful to developers, but it is an implementation dump: it can repeat a
//! shared DAG, include whole memory snapshots, and grow without relation to
//! the useful part of a diagnostic.

use crate::kernel::CResourceFact;
use crate::kernel::{
    AlgebraicTerm, AlgebraicTermNode, AlgebraicValue, AlgebraicValueType, Bitvector32Term,
    CExpressionOutcome, CMemory, CResource, CState, ConditionTerm, IntegerRangeFoldIndex,
    IntegerTerm, Pointer, PointerOffsetTerm, Proposition, PureFunctionArgument, Sort,
    SpecCaptureRefusal, Term, Variable,
};
use std::collections::HashMap;
use std::fmt::Write;

mod legend;
mod surface;
mod trace_facts;

const MAX_BYTES: usize = 32 * 1024;
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 96;
/// How many distinct snapshots one report labels before it stops comparing.
/// Structural equality is bounded independently of identity retention.
/// Proposition displays may name more states through constant-time retained
/// root identities; low-level expression displays stop at this comparison cap.
const MAX_SNAPSHOT_LABELS: usize = 32;

/// Report-local labels for memory snapshots and symbolic values.
///
/// A snapshot used to print the addresses of the five `Arc` roots it is built
/// from, so two structurally identical memories printed as different tuples
/// and a reader could not tell "same memory" from "different memory" — the one
/// thing those labels exist to show. A label is now a small ordinal, assigned
/// in order of first appearance and shared by equal memories, so `snapshot#1`
/// twice means one memory and `snapshot#1`/`snapshot#2` means two. Internal
/// variable IDs likewise become source names when the checked state provides
/// one, or distinct alphabetic labels when it does not.
#[derive(Default)]
pub(crate) struct SnapshotLabels {
    memories: Vec<CMemory>,
    memory_identities: HashMap<(usize, usize, usize, usize, usize), usize>,
    trace_labels: bool,
    pointer_values: HashMap<Pointer, usize>,
    pointer_sources: HashMap<Pointer, String>,
    source_memories: Vec<(CMemory, String, std::rc::Rc<NamingTables>)>,
    source_names: HashMap<Variable, String>,
    source_types: HashMap<Variable, crate::kernel::CType>,
    anonymous_names: HashMap<Variable, String>,
    /// The parameters or locals a diagnostic spells addresses through, with
    /// their values, when the caller has them.
    naming: Option<std::rc::Rc<NamingTables>>,
}

impl SnapshotLabels {
    /// Stable report-local identities, distinct from source spellings.
    pub(crate) fn pointer_value_name(&mut self, pointer: &Pointer) -> String {
        if let Some(index) = self.pointer_values.get(pointer) {
            return format!("value#{index}");
        }
        if self.pointer_values.len() >= 128 {
            return "<value identity omitted: report limit>".into();
        }
        let index = self.pointer_values.len() + 1;
        self.pointer_values.insert(pointer.clone(), index);
        format!("value#{index}")
    }

    /// Labels that read a scalar the tables name as that name, and an
    /// address inside an object the tables name as its source spelling.
    pub(crate) fn naming(
        parameters: &[crate::languages::c::syntax::C0Parameter],
        arguments: &[crate::kernel::CExpression],
    ) -> Self {
        let mut labels = Self::default();
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let crate::kernel::CExpression::Value(value) = argument else {
                continue;
            };
            if let crate::kernel::CValue::Pointer(pointer) = value {
                labels.immutable_pointer_name(pointer.pointer(), parameter.name());
            }
            let term = match value {
                crate::kernel::CValue::Bool(term)
                | crate::kernel::CValue::Int8(term)
                | crate::kernel::CValue::Int16(term)
                | crate::kernel::CValue::Int32(term)
                | crate::kernel::CValue::UInt8(term)
                | crate::kernel::CValue::UInt16(term)
                | crate::kernel::CValue::UInt32(term)
                | crate::kernel::CValue::Int64(term)
                | crate::kernel::CValue::UInt64(term) => term,
                _ => continue,
            };
            if let Bitvector32Term::Variable(variable) = term {
                labels.source_name(
                    *variable,
                    crate::surface::diagnostics::rust_variable_spelling(parameter.name())
                        .unwrap_or_else(|| parameter.name().to_string()),
                );
                labels.source_types.insert(*variable, value.c_type());
            }
        }
        labels.naming = Some(std::rc::Rc::new((parameters.to_vec(), arguments.to_vec())));
        labels
    }

    /// Current locals take precedence over entry values. This is diagnostic
    /// data only; no proof decision consults these names.
    pub(crate) fn with_state(
        parameters: &[crate::languages::c::syntax::C0Parameter],
        arguments: &[crate::kernel::CExpression],
        state: &CState,
    ) -> Self {
        let mut labels = Self::naming(parameters, arguments);
        labels.register_current_state(state);
        labels
    }

    pub(crate) fn register_current_state(&mut self, state: &CState) {
        let (names, values) = crate::surface::diagnostics::local_naming_tables(state);
        let current = Self::naming(&names, &values);
        // A reassigned parameter's entry value is not its current value.
        for (variable, name) in &mut self.source_names {
            if names.iter().any(|local| local.name() == name)
                && !current.source_names.contains_key(variable)
            {
                *name = format!("at(function.entry, {name})");
            }
        }
        for (pointer, name) in &mut self.pointer_sources {
            if names.iter().any(|local| local.name() == name)
                && !current.pointer_sources.contains_key(pointer)
            {
                *name = format!("at(function.entry, {name})");
            }
        }
        for (pointer, name) in current.pointer_sources {
            self.pointer_sources.entry(pointer).or_insert(name);
        }
        self.source_types.extend(current.source_types);
        for (variable, name) in current.source_names {
            self.source_names.entry(variable).or_insert(name);
        }
        self.naming = current.naming;
        self.source_state(state, "current".into());
    }

    pub(crate) fn source_state(&mut self, state: &CState, point: String) {
        if self.source_memories.len() < MAX_SNAPSHOT_LABELS {
            let tables = crate::surface::diagnostics::local_naming_tables(state);
            self.source_memories
                .push((state.memory().clone(), point, std::rc::Rc::new(tables)));
        }
    }

    fn source_memory_context(&self, memory: &CMemory) -> Option<(&str, &NamingTables)> {
        self.source_memories
            .iter()
            .find_map(|(known, point, naming)| {
                // Exact storage roots identify a state without walking memory.
                known
                    .same_storage_roots(memory)
                    .then_some((point.as_str(), naming.as_ref()))
            })
    }

    /// Labels naming what the function being verified declares, when one is.
    pub(crate) fn ambient() -> Self {
        let Some(tables) = AMBIENT_NAMING.with(|naming| naming.borrow().clone()) else {
            return Self::default();
        };
        let mut labels = Self::naming(&tables.0, &tables.1);
        labels.naming = Some(tables);
        labels
    }

    pub(crate) fn naming_tables(
        &self,
    ) -> Option<(
        &[crate::languages::c::syntax::C0Parameter],
        &[crate::kernel::CExpression],
    )> {
        self.naming
            .as_ref()
            .map(|tables| (tables.0.as_slice(), tables.1.as_slice()))
    }

    pub(crate) fn source_name(&mut self, variable: Variable, name: String) {
        self.source_names.entry(variable).or_insert(name);
    }

    fn source_name_for(&self, variable: Variable) -> Option<&str> {
        self.source_names
            .get(&variable)
            .map(String::as_str)
            .filter(|name| name.len() <= 256)
    }

    fn variable_name(&mut self, variable: Variable, kind: &str) -> String {
        if let Some(name) = self.source_names.get(&variable) {
            return name.clone();
        }
        if let Some(name) = self.anonymous_names.get(&variable) {
            return name.clone();
        }
        let name = format!("{kind} {}", alphabetic_label(self.anonymous_names.len()));
        self.anonymous_names.insert(variable, name.clone());
        name
    }

    /// The label of this memory: an existing ordinal when an equal memory has
    /// already been labeled, otherwise the next one.
    fn label(&mut self, memory: &CMemory) -> Option<usize> {
        if let Some(index) = self.memory_identities.get(&memory.diagnostic_identity()) {
            return Some(*index);
        }
        if let Some(index) = self
            .memories
            .iter()
            .take(MAX_SNAPSHOT_LABELS)
            .position(|labeled| labeled.same_storage_roots(memory) || labeled == memory)
        {
            return Some(index + 1);
        }
        let limit = if self.trace_labels {
            MAX_NODES
        } else {
            MAX_SNAPSHOT_LABELS
        };
        if self.memories.len() >= limit {
            return None;
        }
        // Retaining the roots prevents identity reuse during this report.
        self.memories.push(memory.clone());
        self.memory_identities
            .insert(memory.diagnostic_identity(), self.memories.len());
        Some(self.memories.len())
    }

    pub(crate) fn snapshot_name(&mut self, memory: &CMemory) -> String {
        self.label(memory).map_or_else(
            || "snapshot<untracked>".to_owned(),
            |index| format!("snapshot#{index}"),
        )
    }
}

/// Exact Click spelling for a bounded fact whose operands are named source
/// values. Historical reads require their own recorded state's names and an
/// explicit `at(...)`; unknown states and generated values do not qualify.
#[cfg(test)]
pub(crate) fn render_simple_click_fact_labeled(
    proposition: &Proposition,
    labels: &SnapshotLabels,
) -> Option<String> {
    surface::render(proposition, labels)
}

fn alphabetic_label(mut index: usize) -> String {
    let mut letters = Vec::new();
    loop {
        letters.push((b'A' + (index % 26) as u8) as char);
        index /= 26;
        if index == 0 {
            break;
        }
        index -= 1;
    }
    letters.into_iter().rev().collect()
}

/// Identify the actual store where an assumption-free history comparison stops.
/// Use report-wide labels even when no source spelling names the address.
pub(crate) fn render_memory_history_check(
    history: &super::MemoryHistoryDiagnostic,
    labels: &mut SnapshotLabels,
) -> Option<String> {
    use crate::kernel::resource_tracker::{Change, OwnedResource};
    let naming = labels.naming.clone();
    let (parameters, arguments) = naming
        .as_deref()
        .map_or((&[][..], &[][..]), |(p, a)| (p.as_slice(), a.as_slice()));
    let explanation = &history.explanation;
    let (at, stop) = explanation.outcome.blocking_step()?;
    let OwnedResource::Cell {
        pointer: read,
        bytes,
    } = &explanation.resource
    else {
        return None;
    };
    let Change::Store { pointer: written } = &stop.change else {
        return None;
    };
    let at = at?;
    let written_bytes = history.written_bytes?;
    let address = |pointer: &Pointer, labels: &mut SnapshotLabels| {
        crate::surface::diagnostics::diagnostic_source_cell(pointer, parameters, arguments)
            .map(|source| format!("`{source}`"))
            .unwrap_or_else(|| format!("address {}", labels.pointer_value_name(pointer)))
    };
    let written = address(written, labels);
    let read = address(read, labels);
    let snapshot = labels.snapshot_name(at.snapshot().memory());
    Some(format!(
        "memory-history check stops at {snapshot}:\n    store: {} bytes at {written}\n    read range checked: {bytes} bytes at {read}",
        written_bytes,
    ))
}

/// Render one proposition without allowing its shape or attached snapshots to
/// determine the size of the error message.
pub(crate) fn render_proposition(proposition: &Proposition) -> String {
    let mut labels = SnapshotLabels::ambient();
    let mut text = render_proposition_labeled(proposition, &mut labels);
    text.push_str(&labels.trace_legend());
    text
}

type NamingTables = (
    Vec<crate::languages::c::syntax::C0Parameter>,
    Vec<crate::kernel::CExpression>,
);

thread_local! {
    /// The parameters of the C function being verified and their entry
    /// values. Diagnostics only: nothing reads it to decide a proof.
    static AMBIENT_NAMING: std::cell::RefCell<Option<std::rc::Rc<NamingTables>>> =
        const { std::cell::RefCell::new(None) };
}

/// Starts verifying a C function whose parameters hold `arguments`.
pub(crate) fn enter_ambient_naming(
    parameters: &[crate::languages::c::syntax::C0Parameter],
    arguments: &[crate::kernel::CExpression],
) {
    AMBIENT_NAMING.with(|naming| {
        *naming.borrow_mut() = Some(std::rc::Rc::new((parameters.to_vec(), arguments.to_vec())));
    });
}

pub(crate) fn clear_ambient_naming() {
    AMBIENT_NAMING.with(|naming| *naming.borrow_mut() = None);
}

/// A bounded view of one exact resource representation for a proof trace.
#[cfg(test)]
pub(crate) fn render_resource_fact(fact: &CResourceFact) -> String {
    let mut labels = SnapshotLabels::default();
    render_resource_fact_labeled(fact, &mut labels)
}

pub(crate) fn render_resource_fact_labeled(
    fact: &CResourceFact,
    labels: &mut SnapshotLabels,
) -> String {
    labels.trace_labels = true;
    let mut renderer = Renderer {
        output: String::with_capacity(128),
        nodes: 0,
        depth: 0,
        truncated: false,
        labels,
        bound_names: Vec::new(),
        trace_facts: true,
    };
    match fact {
        CResourceFact::Own(resource, quantity) => {
            renderer.push("owns ");
            renderer.resource(resource);
            renderer.push(" x ");
            renderer.bitvector(quantity);
        }
        CResourceFact::View(resource) => {
            renderer.push("views ");
            renderer.resource(resource);
        }
    }
    if renderer.truncated {
        renderer.output.push('…');
    }
    renderer.output
}

/// One proposition display policy for facts, requirements, and goals in both
/// ordinary verifier errors and traces. Source-like spelling is used only when
/// it preserves the checked identities; otherwise the typed renderer names
/// each read's width, snapshot, and address with report-local labels.
pub(crate) fn render_proposition_labeled(
    proposition: &Proposition,
    labels: &mut SnapshotLabels,
) -> String {
    labels.trace_labels = true;
    surface::display(proposition, labels)
        .unwrap_or_else(|| render_kernel_fact(proposition, labels, true))
}

/// Lower-level renderer tests exercise the bounded notation directly.
#[cfg(test)]
pub(crate) fn render_internal_proposition_labeled(
    proposition: &Proposition,
    labels: &mut SnapshotLabels,
) -> String {
    render_kernel_fact(proposition, labels, false)
}

#[cfg(test)]
pub(crate) fn render_trace_fact_labeled(
    proposition: &Proposition,
    labels: &mut SnapshotLabels,
) -> String {
    render_proposition_labeled(proposition, labels)
}

fn render_kernel_fact(
    proposition: &Proposition,
    labels: &mut SnapshotLabels,
    trace_facts: bool,
) -> String {
    let mut renderer = Renderer {
        output: String::with_capacity(1024),
        nodes: 0,
        depth: 0,
        truncated: false,
        labels,
        bound_names: Vec::new(),
        trace_facts,
    };
    renderer.proposition(proposition);
    if renderer.truncated {
        const SUFFIX: &str = "\n… <proof proposition truncated>";
        let limit = MAX_BYTES.saturating_sub(SUFFIX.len());
        let mut end = limit.min(renderer.output.len());
        while end > 0 && !renderer.output.is_char_boundary(end) {
            end -= 1;
        }
        renderer.output.truncate(end);
        renderer.output.push_str(SUFFIX);
    }
    renderer.output
}

/// Render one exact-arithmetic term under the same bounds.
///
/// An `IntegerTerm` can hold a pure-function application or an algebraic
/// elimination, so its `Debug` reaches the same datatype schemas a
/// proposition's does.
pub(crate) fn render_integer_term(term: &IntegerTerm) -> String {
    surface::integer(term, &SnapshotLabels::ambient())
        .unwrap_or_else(|| "Integer term has no exact Click spelling at this frontier".into())
}

/// Render `left operator right` under one set of labels, so two distinct
/// unnamed values on the two sides are told apart and one value read on both
/// sides keeps one name. Rendering each side on its own restarts the labels
/// and spells a model at the loop head and the rebound model alike.
pub(crate) fn render_integer_comparison(
    left: &IntegerTerm,
    operator: &str,
    right: &IntegerTerm,
) -> String {
    let labels = SnapshotLabels::ambient();
    match (
        surface::integer(left, &labels),
        surface::integer(right, &labels),
    ) {
        (Some(left), Some(right)) => format!("{left} {operator} {right}"),
        _ => "Integer comparison has no exact Click spelling at this frontier".into(),
    }
}

/// Describe a refused Integer capture: which written subterm carries an
/// evaluation condition, and which condition the proof context is missing.
pub(crate) fn describe_spec_capture_refusal(refusal: &SpecCaptureRefusal) -> String {
    describe_spec_capture_refusal_labeled(refusal, &mut SnapshotLabels::ambient())
}

pub(crate) fn describe_spec_capture_refusal_labeled(
    refusal: &SpecCaptureRefusal,
    labels: &mut SnapshotLabels,
) -> String {
    match refusal {
        SpecCaptureRefusal::Message(message) => message.clone(),
        SpecCaptureRefusal::Undischarged {
            subterm,
            proposition,
        } => format!(
            "{} denotes this value only where `{}` holds, and that is not available here",
            subterm.describe(),
            render_proposition_labeled(proposition, labels)
        ),
    }
}

struct Renderer<'a> {
    output: String,
    nodes: usize,
    depth: usize,
    truncated: bool,
    labels: &'a mut SnapshotLabels,
    bound_names: Vec<(Variable, String)>,
    trace_facts: bool,
}

impl Renderer<'_> {
    fn variable_name(&mut self, variable: Variable, kind: &str) -> String {
        self.bound_names
            .iter()
            .rev()
            .find(|(bound, _)| *bound == variable)
            .map(|(_, name)| name.clone())
            .unwrap_or_else(|| self.labels.variable_name(variable, kind))
    }

    fn fmt(&mut self, arguments: std::fmt::Arguments<'_>) {
        struct Sink<'a, 'b>(&'a mut Renderer<'b>);
        impl std::fmt::Write for Sink<'_, '_> {
            fn write_str(&mut self, value: &str) -> std::fmt::Result {
                self.0.push(value);
                if self.0.truncated {
                    Err(std::fmt::Error)
                } else {
                    Ok(())
                }
            }
        }
        let _ = Sink(self).write_fmt(arguments);
    }
    fn push(&mut self, text: &str) {
        if self.truncated {
            return;
        }
        let remaining = MAX_BYTES.saturating_sub(self.output.len());
        if text.len() <= remaining {
            self.output.push_str(text);
            return;
        }
        let mut end = remaining.min(text.len());
        while end > 0 && !text.is_char_boundary(end) {
            end -= 1;
        }
        self.output.push_str(&text[..end]);
        self.truncated = true;
    }

    fn visit(&mut self) -> bool {
        if self.truncated {
            return false;
        }
        self.nodes = self.nodes.saturating_add(1);
        if self.nodes > MAX_NODES || self.depth >= MAX_DEPTH {
            self.truncated = true;
            self.push("…");
            return false;
        }
        true
    }

    fn proposition(&mut self, proposition: &Proposition) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match proposition {
            Proposition::Equal(left, right) => self.binary_term(left, " = ", right),
            Proposition::ConditionIs(condition, value) => {
                self.condition(condition);
                self.push(if *value { " is true" } else { " is false" });
            }
            Proposition::Predicate { name, arguments } => {
                if let Some(event) = name.strip_prefix("__click_volatile_write_") {
                    self.push("volatile-write-event#");
                    self.push(event);
                } else {
                    self.push("predicate ");
                    self.push(name);
                }
                self.push("(");
                self.terms(arguments);
                self.push(")");
            }
            Proposition::And(left, right) => self.binary_prop(left, " ∧ ", right),
            Proposition::Or(left, right) => self.binary_prop(left, " ∨ ", right),
            Proposition::Implies(left, right) => self.binary_prop(left, " ⇒ ", right),
            Proposition::Not(body) => {
                self.push("¬(");
                self.proposition(body);
                self.push(")");
            }
            Proposition::ForAll { var, sort, body } => {
                let name = self.variable_name(*var, "bound");
                self.fmt(format_args!("∀{name}:"));
                self.sort(sort);
                self.push(". ");
                self.bound_names.push((*var, name));
                self.proposition(body);
                self.bound_names.pop();
            }
            Proposition::Exists {
                name,
                var,
                sort,
                body,
            } => {
                let binder = if name.is_empty() {
                    self.variable_name(*var, "bound")
                } else {
                    name.clone()
                };
                self.fmt(format_args!("∃{binder}:"));
                self.sort(sort);
                self.push(". ");
                self.bound_names.push((*var, binder));
                self.proposition(body);
                self.bound_names.pop();
            }
            Proposition::CMemoryLoadable {
                memory,
                base,
                bytes,
                wide,
            } => {
                self.push("viewable(memory=");
                self.memory(memory);
                self.push(", base=");
                self.pointer(base);
                self.push(if *wide {
                    ", bytes:uint64="
                } else {
                    ", bytes:uint32="
                });
                self.bitvector(bytes);
                self.push(")");
            }
            Proposition::CMemoryCanStore {
                memory,
                pointer,
                byte_width,
            } => {
                self.push("can-store(memory=");
                self.memory(memory);
                self.push(", pointer=");
                self.pointer(pointer);
                self.fmt(format_args!(", bytes={byte_width})"));
            }
            Proposition::CMemoryInitialized {
                memory,
                base,
                bytes,
            } => {
                self.push("initialized(");
                self.memory(memory);
                self.push(", pointer=");
                self.pointer(base);
                self.fmt(format_args!(", bytes={bytes})"));
            }
            Proposition::CMemoryReadDefined {
                memory, pointer, ..
            } => {
                self.push("defined-read(");
                self.memory(memory);
                self.push(", ");
                self.pointer(pointer);
                self.push(")");
            }
            Proposition::CMemoryLoads {
                memory,
                pointer,
                outcome,
            } => {
                self.push("memory-load(memory=");
                self.memory(memory);
                self.push(", pointer=");
                self.pointer(pointer);
                self.push(", outcome=");
                self.outcome(outcome);
                self.push(")");
            }
            Proposition::CResourceSeparate { left, right } => {
                self.resource(left);
                self.push(" separate ");
                self.resource(right);
            }
            Proposition::CResourceContains { parent, child } => {
                self.resource(parent);
                self.push(" contains ");
                self.resource(child);
            }
            Proposition::CResourceComposition(context) => self.resource_composition(context),
            Proposition::CMemoryMutatesOnly {
                before,
                after,
                writes,
            } => {
                self.push("memory-mutates-only(");
                self.memory(before);
                self.push(" -> ");
                self.memory(after);
                self.push(", writes=");
                for (index, (pointer, bytes)) in writes.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.pointer(pointer);
                    self.push(&format!(" ({bytes} bytes)"));
                }
                self.push(")");
            }
            Proposition::CMemoryEffectSummary {
                before,
                after,
                mutable_ranges,
            } => {
                self.push("memory-effects(");
                self.memory(before);
                self.push(" -> ");
                self.memory(after);
                self.fmt(format_args!(", ranges={})", mutable_ranges.len()));
            }
            Proposition::CHeapAllocationFreed {
                before,
                after,
                allocation_base,
                bytes,
            } => {
                self.push("heap-freed(");
                self.memory(before);
                self.push(" -> ");
                self.memory(after);
                self.push(", base=");
                self.pointer(allocation_base);
                self.push(", bytes=");
                self.bitvector(bytes);
                self.push(")");
            }
            Proposition::CExpressionEvaluates {
                state,
                expression: _,
                outcome,
            } => {
                self.push("expression-evaluates(state=");
                self.state(state);
                self.push(", expression=<C expression>, outcome=");
                self.outcome(outcome);
                self.push(")");
            }
            Proposition::CConditionEvaluates {
                state,
                condition: _,
                outcome,
            } => {
                self.push("condition-evaluates(state=");
                self.state(state);
                self.push(", condition=<C condition>, outcome=");
                self.condition_outcome(outcome);
                self.push(")");
            }
            Proposition::CStatementExecutes {
                state,
                statement: _,
                outcome,
            }
            | Proposition::CStatementVerifies {
                state,
                statement: _,
                outcome,
            } => {
                self.push("statement-");
                self.push(
                    if matches!(proposition, Proposition::CStatementVerifies { .. }) {
                        "verifies"
                    } else {
                        "executes"
                    },
                );
                self.push("(state=");
                self.state(state);
                self.push(", statement=<C statement>, outcome=");
                self.statement_outcome(outcome);
                self.push(")");
            }
            Proposition::CFunctionExecutes {
                state,
                function: _,
                arguments,
                outcome,
            }
            | Proposition::CFunctionVerifies {
                state,
                function: _,
                arguments,
                outcome,
            } => {
                self.push("function-call(state=");
                self.state(state);
                self.fmt(format_args!(
                    ", function=<C function>, args={}, outcome=",
                    arguments.len()
                ));
                self.function_outcome(outcome);
                self.push(")");
            }
            Proposition::CFunctionSatisfiesSpecification { .. } => {
                self.push("function-satisfies(<C function specification>)")
            }
            Proposition::CFunctionPartiallySatisfiesSpecification { .. } => {
                self.push("function-partially-satisfies(<C function specification>)")
            }
        }
        self.depth -= 1;
    }

    fn sort(&mut self, sort: &Sort) {
        match sort {
            Sort::Algebraic(ty) => {
                self.push(&ty.name);
                self.algebraic_type_arguments(&ty.arguments);
            }
            _ => self.fmt(format_args!("{sort:?}")),
        }
    }

    fn algebraic_type_arguments(&mut self, arguments: &[AlgebraicValueType]) {
        if arguments.is_empty() {
            return;
        }
        self.push("<");
        for (index, argument) in arguments.iter().enumerate() {
            if self.truncated {
                break;
            }
            if index > 0 {
                self.push(", ");
            }
            self.algebraic_value_type(argument);
        }
        self.push(">");
    }

    fn algebraic_value_type(&mut self, ty: &AlgebraicValueType) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match ty {
            AlgebraicValueType::Parameter(name) => self.push(name),
            AlgebraicValueType::C(ty) => self.fmt(format_args!("{ty:?}")),
            AlgebraicValueType::Integer => self.push("Integer"),
            AlgebraicValueType::Algebraic { name, arguments } => {
                self.push(name);
                self.algebraic_type_arguments(arguments);
            }
        }
        self.depth -= 1;
    }

    fn binary_prop(&mut self, left: &Proposition, op: &str, right: &Proposition) {
        self.push("(");
        self.proposition(left);
        self.push(op);
        self.proposition(right);
        self.push(")");
    }
    fn binary_term(&mut self, left: &Term, op: &str, right: &Term) {
        self.term(left);
        self.push(op);
        self.term(right);
    }
    fn terms(&mut self, terms: &[Term]) {
        for (index, term) in terms.iter().enumerate() {
            if self.truncated {
                break;
            }
            if index > 0 {
                self.push(", ");
            }
            self.term(term);
        }
    }
    fn term(&mut self, term: &Term) {
        if !self.visit() {
            return;
        }
        match term {
            Term::Condition(c) => self.condition(c),
            Term::Bitvector32(v) => self.bitvector(v),
            Term::Integer(i) => self.integer(i),
            Term::PointerOffset(o) => self.offset(o, 0),
            Term::CValue(v) => self.cvalue(v),
            Term::CExpressionOutcome(o) => self.outcome(o),
            Term::CStatementOutcome(_) => self.push("statement-outcome(<state snapshot>)"),
            Term::CFunctionOutcome(_) => self.push("function-outcome(<state snapshot>)"),
            Term::CMemory(m) => self.memory(m),
            Term::CState(s) => self.state(s),
            Term::Sequence(_) => self.push("sequence(<bounded opaque value>)"),
            Term::Algebraic(value) => self.algebraic(value),
        }
    }

    /// Renders an algebraic term in its source spelling: a constructor, a pure
    /// function application, an elimination, or a binder.
    ///
    /// The datatype's declaration graph is deliberately not rendered. An
    /// `AlgebraicTerm` carries the whole instantiated `AlgebraicSchemas` so the
    /// kernel can check formation without trusting surface names, and printing
    /// that structure repeats every variant of every reachable family for each
    /// occurrence of a value. The type's own name is what a reader needs.
    fn algebraic(&mut self, term: &AlgebraicTerm) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match &term.node {
            AlgebraicTermNode::Variable(variable) => {
                let name = self.variable_name(*variable, "value");
                self.fmt(format_args!("{name}:{}", term.algebraic_type.name))
            }
            AlgebraicTermNode::Constructor { variant, fields } => {
                self.fmt(format_args!("{}::{variant}", term.algebraic_type.name));
                if !fields.is_empty() {
                    self.push("(");
                    for (index, field) in fields.iter().enumerate() {
                        if self.truncated {
                            break;
                        }
                        if index > 0 {
                            self.push(", ");
                        }
                        self.algebraic_value(field);
                    }
                    self.push(")");
                }
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                self.push("match ");
                self.algebraic(scrutinee);
                self.push(" { ");
                for (index, arm) in arms.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&arm.variant);
                    self.push(" => ");
                    self.algebraic(&arm.body);
                }
                self.push(" }");
            }
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                self.pure_arguments(arguments);
                self.push(")");
            }
        }
        self.depth -= 1;
    }

    fn algebraic_value(&mut self, value: &AlgebraicValue) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match value {
            AlgebraicValue::C(value) => self.cvalue(value),
            AlgebraicValue::Integer(value) => self.integer(value),
            AlgebraicValue::Algebraic(value) => self.algebraic(value),
        }
        self.depth -= 1;
    }

    fn pure_arguments(&mut self, arguments: &[PureFunctionArgument]) {
        for (index, argument) in arguments.iter().enumerate() {
            if self.truncated {
                break;
            }
            if index > 0 {
                self.push(", ");
            }
            self.pure_argument(argument);
        }
    }

    fn pure_argument(&mut self, argument: &PureFunctionArgument) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        match argument {
            PureFunctionArgument::Value(value) => self.cvalue(value),
            PureFunctionArgument::Integer(value) => self.integer_shared(value),
            PureFunctionArgument::Algebraic(value) => self.algebraic(value),
            // The snapshot identity is printed, not elided. A goal that
            // compares the same pure function at two states -- a loop
            // invariant about a sequence, or a ranking measure's pre and post
            // -- differs only in this argument's memory, so eliding it
            // rendered `count(a) < count(a)`: a reader could not tell the two
            // sides apart, and a true goal read as a false one.
            PureFunctionArgument::ArrayRef {
                memory,
                pointer,
                element_type,
            } => {
                if self.trace_facts {
                    self.fmt(format_args!(
                        "array-ref<{}>(",
                        crate::kernel::c_type_spelling(*element_type)
                    ));
                } else {
                    self.push("array-ref(");
                }
                self.memory(memory);
                self.push(", ");
                self.cvalue(pointer);
                self.push(")");
            }
        }
        self.depth -= 1;
    }
    fn condition(&mut self, c: &ConditionTerm) {
        match c {
            ConditionTerm::Constant(v) => self.push(if *v { "true" } else { "false" }),
            ConditionTerm::Variable(v) => {
                let name = self.variable_name(*v, "condition");
                self.push(&name);
            }
            crate::kernel::integer_comparison_condition!(a, b) => {
                self.push("integer-condition(");
                self.integer_shared(a);
                self.push(match c {
                    ConditionTerm::IntegerLessThan(..) => " < ",
                    ConditionTerm::IntegerLessEqual(..) => " <= ",
                    ConditionTerm::IntegerGreaterThan(..) => " > ",
                    ConditionTerm::IntegerGreaterEqual(..) => " >= ",
                    ConditionTerm::IntegerEqual(..) => " = ",
                    _ => " != ",
                });
                self.integer_shared(b);
                self.push(")");
            }
            ConditionTerm::Bitvector32SignedLessThan(a, b) => {
                self.binary_condition_bv(a, b, "int32 <")
            }
            ConditionTerm::Bitvector32SignedLessEqual(a, b) => {
                self.binary_condition_bv(a, b, "int32 <=")
            }
            ConditionTerm::Bitvector32SignedGreaterThan(a, b) => {
                self.binary_condition_bv(a, b, "int32 >")
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(a, b) => {
                self.binary_condition_bv(a, b, "int32 >=")
            }
            ConditionTerm::Bitvector32Equal(a, b) => self.binary_condition_bv(a, b, "int32 ="),
            ConditionTerm::Bitvector64Equal(a, b) => self.binary_condition_bv(a, b, "bits64 ="),
            ConditionTerm::Bitvector64SignedLessThan(a, b) => {
                self.binary_condition_bv(a, b, "int64 <")
            }
            ConditionTerm::Bitvector64SignedLessEqual(a, b) => {
                self.binary_condition_bv(a, b, "int64 <=")
            }
            ConditionTerm::Bitvector64SignedGreaterThan(a, b) => {
                self.binary_condition_bv(a, b, "int64 >")
            }
            ConditionTerm::Bitvector64SignedGreaterEqual(a, b) => {
                self.binary_condition_bv(a, b, "int64 >=")
            }
            ConditionTerm::Bitvector64UnsignedLessThan(a, b) => {
                self.binary_condition_bv(a, b, "uint64 <")
            }
            ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => {
                self.binary_condition_bv(a, b, "uint64 <=")
            }
            ConditionTerm::Bitvector64UnsignedGreaterThan(a, b) => {
                self.binary_condition_bv(a, b, "uint64 >")
            }
            ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => {
                self.binary_condition_bv(a, b, "uint64 >=")
            }
            ConditionTerm::AlgebraicEqual(a, b) => {
                self.algebraic(a);
                self.push(" = ");
                self.algebraic(b);
            }
            ConditionTerm::PointerOffsetEqual(a, b) => {
                self.offset(a, 0);
                self.push(" = ");
                self.offset(b, 0);
            }
            ConditionTerm::PointerEqual(a, b) => {
                self.pointer(a);
                self.push(" = ");
                self.pointer(b);
            }
            // Definedness of a partial machine operation is the condition a
            // capture or evaluation refusal most often names, so print the
            // operation instead of a placeholder.
            ConditionTerm::Bitvector32SignedAddOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "+")
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "-")
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "*")
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "/")
            }
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int32", "<<")
            }
            ConditionTerm::Bitvector64SignedAddOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "+")
            }
            ConditionTerm::Bitvector64SignedSubtractOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "-")
            }
            ConditionTerm::Bitvector64SignedMultiplyOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "*")
            }
            ConditionTerm::Bitvector64SignedDivideOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "/")
            }
            ConditionTerm::Bitvector64SignedShiftLeftOverflows(a, b) => {
                self.overflow_condition_bv(a, b, "int64", "<<")
            }
            _ => self.push("condition(<bounded operation>)"),
        }
    }
    fn binary_condition_bv(&mut self, a: &Bitvector32Term, b: &Bitvector32Term, label: &str) {
        // A signed order of sign-flipped operands is the unsigned order of
        // the operands themselves; a constant operand arrives already
        // flipped. Render what it means, not the bias.
        const SIGN_BIT: u32 = 0x8000_0000;
        fn flipped(term: &Bitvector32Term) -> Option<&Bitvector32Term> {
            match term {
                Bitvector32Term::BitwiseXor(value, sign)
                | Bitvector32Term::BitwiseXor(sign, value)
                    if sign.as_const() == Some(SIGN_BIT) =>
                {
                    Some(value)
                }
                _ => None,
            }
        }
        let unflipped = |term: &Bitvector32Term| {
            flipped(term).cloned().or_else(|| {
                term.as_const()
                    .map(|value| Bitvector32Term::Constant(value ^ SIGN_BIT))
            })
        };
        if let Some(order) = label.strip_prefix("int32 ").filter(|order| *order != "=")
            && (flipped(a).is_some() || flipped(b).is_some())
            && let (Some(a), Some(b)) = (unflipped(a), unflipped(b))
        {
            self.push("uint32 ");
            self.push(order);
            self.push("(");
            self.bitvector(&a);
            self.push(", ");
            self.bitvector(&b);
            self.push(")");
            return;
        }
        self.push(label);
        self.push("(");
        self.bitvector(a);
        self.push(", ");
        self.bitvector(b);
        self.push(")");
    }
    fn overflow_condition_bv(
        &mut self,
        a: &Bitvector32Term,
        b: &Bitvector32Term,
        width: &str,
        operator: &str,
    ) {
        self.push(width);
        self.push(" overflow(");
        self.bitvector(a);
        self.push(" ");
        self.push(operator);
        self.push(" ");
        self.bitvector(b);
        self.push(")");
    }
    fn integer(&mut self, i: &IntegerTerm) {
        if self.truncated {
            return;
        }
        match i {
            IntegerTerm::Constant(value) if value.bits() > 256 => {
                self.fmt(format_args!("<integer constant: {} bits>", value.bits()))
            }
            IntegerTerm::Constant(value) => self.fmt(format_args!("{value}")),
            // An Integer model field prints as the field it is; the mint
            // registered it, because the value lives inside the instance fact
            // and the term carries nothing to recover it from.
            IntegerTerm::Variable(variable) => {
                match crate::kernel::model_fields::model_field_spelling(*variable) {
                    Some(spelling) => self.push(&spelling),
                    None => {
                        let name = self.variable_name(*variable, "integer");
                        self.push(&name);
                    }
                }
            }
            IntegerTerm::Machine(value) => {
                self.fmt(format_args!("machine-integer<{:?}>(", value.ty()));
                self.bitvector(value.value());
                self.push(")");
            }
            IntegerTerm::Negate(value) => {
                self.push("(-");
                self.integer_shared(value);
                self.push(")");
            }
            IntegerTerm::Add(left, right) => self.integer_binary(left, "+", right),
            IntegerTerm::Subtract(left, right) => self.integer_binary(left, "-", right),
            IntegerTerm::Multiply(left, right) => self.integer_binary(left, "*", right),
            IntegerTerm::TruncatingQuotient(left, right)
            | IntegerTerm::TruncatingRemainder(left, right) => {
                self.push(if matches!(i, IntegerTerm::TruncatingQuotient(_, _)) {
                    "truncating_quotient("
                } else {
                    "truncating_remainder("
                });
                self.integer_shared(left);
                self.push(", ");
                self.integer_shared(right);
                self.push(")");
            }
            IntegerTerm::PureFunctionApplication(application) => {
                self.push(application.name());
                self.push("(");
                self.pure_arguments(application.arguments());
                self.push(")");
            }
            IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
                self.push("match ");
                self.algebraic(scrutinee);
                self.push(" { ");
                for (index, arm) in arms.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&arm.variant);
                    self.push(" => ");
                    self.integer_shared(&arm.body);
                }
                self.push(" }");
            }
            IntegerTerm::RangeFold {
                index,
                initial,
                accumulator,
                item,
                body,
            } => {
                self.push("range-fold(index=");
                match index {
                    IntegerRangeFoldIndex::Int32 { start, end }
                    | IntegerRangeFoldIndex::UInt64 { start, end } => {
                        self.bitvector(start.value());
                        self.push("..");
                        self.bitvector(end.value());
                    }
                    IntegerRangeFoldIndex::Integer { start, end } => {
                        self.integer_shared(start);
                        self.push("..");
                        self.integer_shared(end);
                    }
                }
                self.push(", acc=acc, item=item, init=");
                self.integer_shared(initial);
                self.push(", body=");
                self.bound_names.push((*accumulator, "acc".into()));
                self.bound_names.push((*item, "item".into()));
                self.integer_shared(body);
                self.bound_names.pop();
                self.bound_names.pop();
                self.push(")");
            }
        }
    }
    fn integer_shared(&mut self, value: &crate::kernel::SharedIntegerTerm) {
        if !self.visit() {
            return;
        }
        self.depth += 1;
        self.integer(value.as_ref());
        self.depth -= 1;
    }
    fn integer_binary(
        &mut self,
        left: &crate::kernel::SharedIntegerTerm,
        op: &str,
        right: &crate::kernel::SharedIntegerTerm,
    ) {
        self.push("(");
        self.integer_shared(left);
        self.push(op);
        self.integer_shared(right);
        self.push(")");
    }
    fn bitvector(&mut self, v: &Bitvector32Term) {
        if self.truncated || !self.visit() || self.depth >= MAX_DEPTH {
            self.truncated = true;
            return;
        }
        self.depth += 1;
        if let Bitvector32Term::MemoryLoad(snapshot, pointer, kind) = v {
            // `memory` prints its own `snapshot=` prefix.
            if self.trace_facts {
                self.fmt(format_args!("read<{kind:?}>("));
            } else {
                self.push("load(");
            }
            self.memory(snapshot.as_ref());
            self.push(", pointer=");
            self.pointer(pointer);
            self.push(")");
            self.depth -= 1;
            return;
        }
        // A registered load variable is a name for one load, and the load it
        // names is the part a reader compares. Printing the bare id made two
        // reads of one address at two snapshots look like two unrelated
        // numbers, and printing only the address made them look identical;
        // neither says which memory each side reads, which is the whole
        // question wherever a load fact fails to carry across a step.
        if let Bitvector32Term::Variable(variable) = v
            && crate::kernel::is_load_variable(variable)
            && let Some((snapshot, pointer)) = crate::kernel::registered_load_for_variable(variable)
        {
            let name = self.variable_name(*variable, "load");
            if self.trace_facts {
                let kind = crate::kernel::registered_load_kind_for_variable(variable)
                    .map(|kind| format!("{kind:?}"))
                    .unwrap_or_else(|| "unrecorded type".into());
                self.fmt(format_args!("{name}=read<{kind}>("));
            } else {
                self.fmt(format_args!("{name}=load("));
            }
            self.memory(snapshot.memory());
            self.push(", pointer=");
            self.pointer(&pointer);
            self.push(")");
            self.depth -= 1;
            return;
        }
        match v {
            Bitvector32Term::Constant(v) => self.fmt(format_args!("{v}")),
            Bitvector32Term::Int64Constant(v) => self.fmt(format_args!("{v}i64")),
            Bitvector32Term::UInt64Constant(v) => self.fmt(format_args!("{v}u64")),
            // A model-field variable is a name for one field of one instance,
            // and the field is the part a reader compares. The id is kept
            // beside it here, as a load variable's is, because this renderer
            // prints the kernel's own goal and premises.
            Bitvector32Term::Variable(v)
                if let Some(spelling) = crate::kernel::model_fields::model_field_spelling(*v) =>
            {
                let name = self.variable_name(*v, "value");
                self.fmt(format_args!("{name}={spelling}"))
            }
            Bitvector32Term::Variable(v) => {
                let name = self.variable_name(*v, "value");
                self.push(&name);
            }
            Bitvector32Term::Add(a, b) => self.binary_bv("+", a, b),
            Bitvector32Term::Subtract(a, b) => self.binary_bv("-", a, b),
            Bitvector32Term::Multiply(a, b) => self.binary_bv("*", a, b),
            _ if self.machine_operation(v) => {}
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => {
                self.push("fold(");
                self.bitvector(start);
                self.push("..");
                self.bitvector(end);
                self.push(", init=");
                self.bitvector(initial);
                self.push(", acc=acc, item=item, body=");
                self.bound_names.push((*accumulator, "acc".into()));
                self.bound_names.push((*item, "item".into()));
                self.bitvector(body);
                self.bound_names.pop();
                self.bound_names.pop();
                self.push(")");
            }
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                for (index, argument) in arguments.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.bitvector(argument);
                }
                self.push(")");
            }
            Bitvector32Term::ClickFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                self.pure_arguments(arguments);
                self.push(")");
            }
            Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
                self.push("match ");
                self.algebraic(scrutinee);
                self.push(" { ");
                for (index, arm) in arms.iter().enumerate() {
                    if self.truncated {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.push(&arm.variant);
                    self.push(" => ");
                    self.bitvector(&arm.body);
                }
                self.push(" }");
            }
            Bitvector32Term::PointerAddress(pointer) => {
                self.push("address(");
                self.pointer(pointer);
                self.push(")");
            }
            _ => self.push("bitvector(<bounded opaque operation>)"),
        }
        self.depth -= 1;
    }
    fn binary_bv(&mut self, op: &str, left: &Bitvector32Term, right: &Bitvector32Term) {
        self.push("(");
        self.bitvector(left);
        self.push(op);
        self.bitvector(right);
        self.push(")");
    }
    fn offset(&mut self, o: &PointerOffsetTerm, _depth: usize) {
        if self.depth >= MAX_DEPTH || self.truncated {
            self.truncated = true;
            return;
        }
        match o {
            PointerOffsetTerm::Constant(v) => self.fmt(format_args!("{v}")),
            PointerOffsetTerm::Variable(v) => {
                let name = self.variable_name(*v, "offset");
                self.push(&name);
            }
            PointerOffsetTerm::Add(a, b) => {
                self.depth += 1;
                self.push("(");
                self.offset(a, 0);
                self.push("+");
                self.offset(b, 0);
                self.push(")");
                self.depth -= 1;
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                self.push("int32(");
                self.bitvector(value);
                self.fmt(format_args!(")*{byte_width} bytes"));
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                self.push(if *unsigned { "uint64(" } else { "int64(" });
                self.bitvector(value);
                self.fmt(format_args!(")*{byte_width} bytes"));
            }
        }
    }
    fn pointer(&mut self, p: &Pointer) {
        if self.trace_facts {
            let name = if p == &Pointer::null() {
                "0".into()
            } else if crate::surface::proof_trace::pointer_definition(p).is_some() {
                self.labels.pointer_value_name(p)
            } else if let Some(name) = self.labels.pointer_sources.get(p) {
                name.clone()
            } else {
                self.labels.pointer_value_name(p)
            };
            self.push(&name);
            return;
        }
        if let Some(definition) = crate::surface::proof_trace::pointer_definition(p) {
            let name = self.labels.pointer_value_name(p);
            self.push(&name);
            self.push("=");
            self.bitvector(&definition);
            return;
        }
        // An address inside an object the caller's tables name reads as its
        // source spelling, not as a block and an offset.
        if let Some(tables) = self.labels.naming.clone() {
            let (parameters, arguments) = &*tables;
            let spelled = crate::surface::diagnostics::describe_pointer(p, parameters, arguments);
            if !spelled.contains("the pointer value at this program point")
                && !spelled.contains('…')
            {
                self.push(&spelled);
                return;
            }
        }
        self.push("pointer(");
        match &p.block {
            crate::kernel::PointerBlock::PureFunctionApplication(application) => {
                self.push(application.name());
                self.push("(");
                self.pure_arguments(application.arguments());
                self.push(")");
            }
            crate::kernel::PointerBlock::Concrete(s) | crate::kernel::PointerBlock::Function(s) => {
                self.push(s)
            }
            crate::kernel::PointerBlock::Heap(id) => self.fmt(format_args!("heap#{id}")),
            crate::kernel::PointerBlock::Temporary(id) => self.fmt(format_args!("temporary#{id}")),
            crate::kernel::PointerBlock::Symbolic(v)
            | crate::kernel::PointerBlock::FunctionSymbolic(v)
            | crate::kernel::PointerBlock::ExternalObject(v) => {
                let name = self.variable_name(*v, "pointer");
                self.push(&name);
            }
            crate::kernel::PointerBlock::ExternalArgument => self.push("external"),
            crate::kernel::PointerBlock::LoadedPointer(identity) => {
                self.fmt(format_args!("loaded-pointer#{}", identity.0))
            }
            crate::kernel::PointerBlock::StringLiteral { identity, .. } => self.push(identity),
        };
        self.push("+");
        self.offset(&p.offset, 0);
        self.push(")");
    }
    fn resource(&mut self, resource: &CResource) {
        match resource {
            CResource::MutexGuard(_) => self.push("mutex-guard"),
            CResource::MutexLive(_) => self.push("mutex-live"),
            CResource::MutexUse(identity) => {
                self.push("mutex_use(");
                self.pointer(identity.mutex());
                self.push(")");
            }
            CResource::Publication(right) => {
                self.push(right.side().keyword());
                self.push("(");
                self.pointer(right.flag());
                self.push(", ");
                self.push(right.payload().family());
                self.push(")");
            }
            CResource::PopulationAuthority(description) => {
                self.push("authority(");
                self.push(description.family());
                self.push("(");
                for (index, argument) in description.arguments().iter().enumerate() {
                    if index > 0 {
                        self.push(", ");
                    }
                    self.algebraic_value(argument);
                }
                if let Some(arity) = description.population_arity() {
                    for _ in 1..arity {
                        self.push(", _");
                    }
                }
                self.push("))");
            }
            CResource::Memory(range) => {
                self.push("memory(");
                self.pointer(range.base());
                self.fmt(format_args!("[{:?}:", range.kind()));
                self.bitvector(range.bound_terms().0);
                self.push("..");
                self.bitvector(range.bound_terms().1);
                self.fmt(format_args!("], stride={})", range.element_width()));
            }
            CResource::Composite { name, arguments } | CResource::Token { name, arguments } => {
                self.push(name);
                self.resource_arguments(arguments);
            }
            CResource::Instance(instance) => {
                self.push("{");
                let identity = self.variable_name(instance.identity(), "instance");
                self.push(&identity);
                self.push(": ");
                self.push(instance.name());
                self.resource_arguments(instance.arguments());
                self.push(", fields=");
                self.resource_arguments(instance.fields());
                if !instance.resource_arguments().is_empty() {
                    self.fmt(format_args!(
                        ", {} resource references omitted",
                        instance.resource_arguments().len()
                    ));
                }
                self.push("}");
            }
            CResource::Iterated(iterated) => {
                self.push("iterated-resource(");
                self.push(iterated.owner());
                self.push(", ");
                self.bitvector(iterated.lower());
                self.push("..");
                self.bitvector(iterated.upper());
                self.push(")");
            }
        }
    }

    fn memory(&mut self, memory: &CMemory) {
        match self.labels.label(memory) {
            Some(label) => self.fmt(format_args!("snapshot#{label}")),
            None => self.push("snapshot<untracked>"),
        }
    }
    fn state(&mut self, state: &CState) {
        self.push("state(");
        self.memory(state.memory());
        self.push(")");
    }
    fn cvalue(&mut self, value: &crate::kernel::CValue) {
        match value {
            crate::kernel::CValue::Void => self.push("void"),
            crate::kernel::CValue::Bool(v) => {
                self.push("bool(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int128(v) => {
                self.push("int128(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt128(v) => {
                self.push("uint128(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int8(v) => {
                self.push("int8(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int16(v) => {
                self.push("int16(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int32(v) => {
                self.push("int32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt8(v) => {
                self.push("uint8(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt16(v) => {
                self.push("uint16(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt32(v) => {
                self.push("uint32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Int64(v) => {
                self.push("int64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::UInt64(v) => {
                self.push("uint64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Float32(v) => {
                self.push("float32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Float64(v) => {
                self.push("float64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::CValue::Pointer(p) => {
                if self.trace_facts {
                    self.fmt(format_args!(
                        "ptr<{}>(",
                        crate::kernel::c_type_spelling(p.c_type())
                    ));
                    self.pointer(p);
                    self.push(")");
                } else {
                    self.pointer(p);
                }
            }
        }
    }
    fn outcome(&mut self, outcome: &CExpressionOutcome) {
        match outcome {
            CExpressionOutcome::Value(value) => self.cvalue(value),
            CExpressionOutcome::UndefinedBehavior(_) => self.push("undefined-behavior"),
            CExpressionOutcome::RuntimeError(_) => self.push("runtime-error"),
        }
    }
    fn condition_outcome(&mut self, outcome: &crate::kernel::CConditionOutcome) {
        self.push(match outcome {
            crate::kernel::CConditionOutcome::Value(true) => "true",
            crate::kernel::CConditionOutcome::Value(false) => "false",
            crate::kernel::CConditionOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::CConditionOutcome::RuntimeError(_) => "runtime-error",
        });
    }
    fn statement_outcome(&mut self, outcome: &crate::kernel::CStatementOutcome) {
        self.push(match outcome {
            crate::kernel::CStatementOutcome::Normal(_) => "normal",
            crate::kernel::CStatementOutcome::Break(_) => "break",
            crate::kernel::CStatementOutcome::Continue(_) => "continue",
            crate::kernel::CStatementOutcome::Jump { .. } => "jump",
            crate::kernel::CStatementOutcome::Return { .. } => "return",
            crate::kernel::CStatementOutcome::Throw { .. } => "throw",
            crate::kernel::CStatementOutcome::VerificationDiverges => "verification-diverges",
            crate::kernel::CStatementOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::CStatementOutcome::RuntimeError(_) => "runtime-error",
        });
    }
    fn function_outcome(&mut self, outcome: &crate::kernel::CFunctionOutcome) {
        self.push(match outcome {
            crate::kernel::CFunctionOutcome::Return { .. } => "return",
            crate::kernel::CFunctionOutcome::Throw { .. } => "throw",
            crate::kernel::CFunctionOutcome::VerificationDiverges => "verification-diverges",
            crate::kernel::CFunctionOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::CFunctionOutcome::RuntimeError(_) => "runtime-error",
        });
    }
}

#[cfg(test)]
mod tests {
    use super::render_internal_proposition_labeled as render_proposition_labeled;
    use super::*;
    use crate::kernel::SharedIntegerTerm;

    fn render_proposition(proposition: &Proposition) -> String {
        render_proposition_labeled(proposition, &mut SnapshotLabels::ambient())
    }

    #[test]
    fn renders_integer_fold_and_scope() {
        let integer = IntegerTerm::Add(
            SharedIntegerTerm::from(IntegerTerm::from(2)),
            SharedIntegerTerm::from(IntegerTerm::from(3)),
        );
        let proposition = Proposition::ForAll {
            var: crate::kernel::Variable(7),
            sort: crate::kernel::Sort::Integer,
            body: Box::new(Proposition::Equal(
                Term::Integer(integer),
                Term::Integer(IntegerTerm::from(5)),
            )),
        };
        let rendered = render_proposition(&proposition);
        assert!(rendered.contains("∀bound A:Integer"), "{rendered}");
        assert!(rendered.contains("2"));
    }

    #[test]
    fn source_names_and_report_local_names_replace_variable_ids() {
        let mut labels = SnapshotLabels::default();
        labels.source_name(Variable(7), "cur".into());
        let proposition = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(Variable(7))),
                Box::new(Bitvector32Term::Variable(Variable(8))),
            ),
            true,
        );
        let first = render_proposition_labeled(&proposition, &mut labels);
        let second = render_proposition_labeled(&proposition, &mut labels);
        assert_eq!(first, second);
        assert!(first.contains("cur"), "{first}");
        assert!(first.contains("value A"), "{first}");
        assert!(!first.contains("v7") && !first.contains("v8"), "{first}");
    }

    #[test]
    fn existential_algebraic_sort_omits_constructor_schema() {
        let mut path = crate::kernel::AlgebraicType::parameter("Path".into());
        path.rigid = false;
        path.arguments = vec![AlgebraicValueType::Integer];
        let proposition = Proposition::Exists {
            name: "path".into(),
            var: Variable(7),
            sort: Sort::Algebraic(path),
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            )),
        };
        let rendered = render_proposition(&proposition);
        assert!(rendered.starts_with("∃path:Path<Integer>. "), "{rendered}");
        assert!(!rendered.contains("AlgebraicSchemas"), "{rendered}");
        assert_eq!(
            crate::surface::diagnostics::describe_pure_fact(&proposition, &[], &[]),
            "∃path:Path<Integer>. true is true"
        );
    }

    #[test]
    fn click_fact_spelling_requires_named_non_load_operands() {
        let mut labels = SnapshotLabels::default();
        labels.source_name(Variable(7), "r".into());
        let equality = |variable| {
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                false,
            )
        };
        assert_eq!(
            render_simple_click_fact_labeled(&equality(Variable(7)), &labels),
            Some("r != 0".into())
        );
        assert_eq!(
            render_simple_click_fact_labeled(&equality(Variable(8)), &labels),
            None
        );
    }

    #[test]
    fn deep_dag_is_bounded_and_marks_truncation() {
        let mut proposition = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        for _ in 0..128 {
            proposition = Proposition::Not(Box::new(proposition));
        }
        let rendered = render_proposition(&proposition);
        assert!(rendered.len() <= MAX_BYTES + "\n… <proof proposition truncated>".len());
        assert!(rendered.contains("truncated") || rendered.contains('…'));
    }

    #[test]
    fn integer_comparison_keeps_operands_and_operator() {
        let left = SharedIntegerTerm::from(IntegerTerm::from(11));
        let right = SharedIntegerTerm::from(IntegerTerm::from(19));
        let proposition =
            Proposition::ConditionIs(ConditionTerm::IntegerLessThan(left, right), true);
        let rendered = render_proposition(&proposition);
        assert!(rendered.contains("integer-condition"));
        assert!(rendered.contains("<"));
        assert!(rendered.contains("11"));
        assert!(rendered.contains("19"));
    }

    #[test]
    fn range_fold_keeps_bounds_and_body_variables() {
        let fold = Bitvector32Term::RangeFold {
            start: Box::new(Bitvector32Term::Constant(1)),
            end: Box::new(Bitvector32Term::Constant(4)),
            initial: Box::new(Bitvector32Term::Constant(0)),
            accumulator: crate::kernel::Variable(8),
            item: crate::kernel::Variable(9),
            body: Box::new(Bitvector32Term::Variable(crate::kernel::Variable(10))),
        };
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(fold),
            Term::Bitvector32(Bitvector32Term::Constant(0)),
        ));
        assert!(rendered.contains("fold("));
        assert!(rendered.contains("acc=acc, item=item"), "{rendered}");
        assert!(rendered.contains("body=value A"), "{rendered}");
    }

    fn loadable_at(memory: CMemory) -> Proposition {
        Proposition::CMemoryLoadable {
            memory,
            base: Pointer {
                block: crate::kernel::PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(1),
            wide: false,
        }
    }

    /// A label says what a reader needs it to say: equal memory reads as one
    /// snapshot whether or not it shares storage roots, and memory that differs
    /// reads as another. The five `Arc` addresses this used to print made two
    /// separately built empty snapshots look like different memory.
    #[test]
    fn equal_snapshots_share_one_label_and_different_memory_does_not() {
        let first = CMemory::default();
        let shared = first.clone();
        let rebuilt = CMemory::default();
        let different = CMemory::new().with_block("block", 16);
        assert_ne!(first.diagnostic_identity(), rebuilt.diagnostic_identity());

        let first_text = render_proposition(&loadable_at(first));
        assert!(first_text.contains("snapshot#1"), "{first_text}");
        assert_eq!(first_text, render_proposition(&loadable_at(shared)));
        assert_eq!(first_text, render_proposition(&loadable_at(rebuilt)));

        // Within one report the labels are the order of first appearance, so
        // two different memories are visibly two.
        let mut labels = SnapshotLabels::default();
        let empty = render_proposition_labeled(&loadable_at(CMemory::default()), &mut labels);
        let blocked = render_proposition_labeled(&loadable_at(different), &mut labels);
        assert!(empty.contains("snapshot#1"), "{empty}");
        assert!(blocked.contains("snapshot#2"), "{blocked}");
    }

    /// The comparison stops at its cap rather than growing with the report.
    #[test]
    fn snapshot_labels_stop_comparing_past_their_cap() {
        let mut labels = SnapshotLabels::default();
        for size in 0..MAX_SNAPSHOT_LABELS as u32 {
            let memory = CMemory::new().with_block(format!("block{size}"), 16);
            assert_eq!(labels.label(&memory), Some(size as usize + 1));
        }
        let overflowing = CMemory::new().with_block("block0", 16);
        assert_eq!(
            labels.label(&overflowing),
            Some(1),
            "an earlier label still wins"
        );
        let beyond = CMemory::new().with_block("beyond", 16);
        assert_eq!(labels.label(&beyond), None);
        let rendered = render_proposition_labeled(&loadable_at(beyond), &mut labels);
        assert!(rendered.contains("snapshot<untracked>"), "{rendered}");
    }

    #[test]
    fn non_ascii_truncation_is_safe() {
        let proposition = Proposition::Predicate {
            name: "λ".repeat(MAX_BYTES),
            arguments: Vec::new(),
        };
        let rendered = render_proposition(&proposition);
        assert!(rendered.is_char_boundary(rendered.len()));
        assert!(rendered.contains("truncated"));
    }

    #[test]
    fn bounded_shared_integer_dag() {
        for depth in [8usize, 16, 32, 64] {
            let mut child =
                SharedIntegerTerm::from(IntegerTerm::Variable(crate::kernel::Variable(1)));
            for _ in 0..depth {
                child = SharedIntegerTerm::from(IntegerTerm::Add(child.clone(), child));
            }
            let rendered = render_proposition(&Proposition::Equal(
                Term::Integer(child.as_ref().clone()),
                Term::Integer(IntegerTerm::from(0)),
            ));
            assert!(rendered.len() <= MAX_BYTES + 64);
            if depth >= 32 {
                assert!(rendered.contains("truncated"));
            }
        }
    }

    #[test]
    fn deep_bitvector_tree_is_bounded() {
        let mut value = Bitvector32Term::Constant(1);
        for _ in 0..128 {
            value = Bitvector32Term::Add(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
        }
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(value),
            Term::Bitvector32(Bitvector32Term::Constant(0)),
        ));
        assert!(rendered.contains("truncated"));
    }

    #[test]
    fn integer_range_fold_renders_bounds_and_body() {
        let start = SharedIntegerTerm::from(IntegerTerm::from(2));
        let end = SharedIntegerTerm::from(IntegerTerm::from(9));
        let body = SharedIntegerTerm::from(IntegerTerm::Add(
            SharedIntegerTerm::from(IntegerTerm::Variable(crate::kernel::Variable(8))),
            SharedIntegerTerm::from(IntegerTerm::Variable(crate::kernel::Variable(9))),
        ));
        let fold = IntegerTerm::RangeFold {
            index: IntegerRangeFoldIndex::Integer { start, end },
            initial: SharedIntegerTerm::from(IntegerTerm::from(0)),
            accumulator: crate::kernel::Variable(8),
            item: crate::kernel::Variable(9),
            body,
        };
        let rendered = render_proposition(&Proposition::Equal(
            Term::Integer(fold),
            Term::Integer(IntegerTerm::from(0)),
        ));
        assert!(rendered.contains("2"));
        assert!(rendered.contains("9"));
        assert!(rendered.contains("acc=acc, item=item"), "{rendered}");
        assert!(rendered.contains("body=(acc+item)"), "{rendered}");
    }

    #[test]
    fn machine_and_c_value_types_remain_visible() {
        let int32 = render_proposition(&Proposition::Equal(
            Term::CValue(crate::kernel::CValue::Int32(Bitvector32Term::Constant(1))),
            Term::CValue(crate::kernel::CValue::UInt32(Bitvector32Term::Constant(1))),
        ));
        assert!(int32.contains("int32(1)"));
        assert!(int32.contains("uint32(1)"));
    }

    #[test]
    fn trace_resource_names_its_arguments_without_debug_state() {
        let resource = CResourceFact::View(CResource::Token {
            name: "child_ref".into(),
            arguments: std::sync::Arc::from([AlgebraicValue::C(crate::kernel::CValue::Int32(
                Bitvector32Term::Constant(7),
            ))]),
        });
        assert_eq!(render_resource_fact(&resource), "views child_ref(int32(7))");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    use crate::kernel::CMemoryRange;
    // Even fallback rendering may receive native memory resources.
    #[test]
    fn wide_resource_diagnostics_keep_the_high_bits_of_bounds() {
        let wide = CMemoryRange::new_wide(
            Pointer::symbolic(Variable(985_500)),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            4,
        );
        let fact = Proposition::CResourceContains {
            parent: Box::new(CResource::Memory(wide.clone())),
            child: Box::new(CResource::Memory(wide)),
        };
        let text = render_internal_proposition_labeled(&fact, &mut SnapshotLabels::default());
        assert!(text.contains("8589934592"), "{text}");
    }
}
