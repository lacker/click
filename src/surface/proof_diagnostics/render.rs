//! A bounded renderer for kernel propositions used in proof failure reports.
//!
//! This deliberately has its own small printer.  `Debug` for a proposition is
//! useful to developers, but it is an implementation dump: it can repeat a
//! shared DAG, include whole memory states, and grow without relation to
//! the useful part of a diagnostic.

use crate::kernel::MachineCastSpelling;
use crate::kernel::ResourceFact;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{
    AlgebraicTerm, AlgebraicTermNode, AlgebraicValue, AlgebraicValueType, ConditionTerm,
    ExecutionState, ExpressionOutcome, IntegerRangeFoldIndex, IntegerTerm, MachineTerm, Memory,
    Pointer, PointerOffsetTerm, Proposition, PureFunctionArgument, Resource, Sort,
    SpecCaptureRefusal, Term, Variable,
};
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, uint64_constant,
};
use crate::surface::ParameterBinding;
use std::collections::HashMap;
use std::fmt::Write;

mod legend;
mod range_collisions;
mod surface;
mod trace_facts;

const MAX_BYTES: usize = 32 * 1024;
const MAX_NODES: usize = 4096;
const MAX_DEPTH: usize = 96;
/// How many distinct states one report labels before it stops comparing.
/// Structural equality is bounded independently of identity retention.
/// Proposition displays may name more states through constant-time retained
/// root identities; low-level expression displays stop at this comparison cap.
const MAX_MEMORY_STATE_LABELS: usize = 32;

/// Report-local labels for memory states and symbolic values.
///
/// A state used to print the addresses of the five `Arc` roots it is built
/// from, so two structurally identical memories printed as different tuples
/// and a reader could not tell "same memory" from "different memory" — the one
/// thing those labels exist to show. A label is now a small ordinal, assigned
/// in order of first appearance and shared by equal memories, so `state#1`
/// twice means one memory and `state#1`/`state#2` means two. Internal
/// variable IDs likewise become source names when the checked state provides
/// one, or distinct alphabetic labels when it does not.
#[derive(Clone, Default)]
pub(crate) struct MemoryStateLabels {
    memories: Vec<Memory>,
    memory_identities: HashMap<(usize, usize, usize, usize, usize), usize>,
    trace_labels: bool,
    range_collisions: Option<range_collisions::RangeCollisions>,
    pointer_values: HashMap<Pointer, usize>,
    pointer_sources: HashMap<Pointer, String>,
    source_memories: Vec<(Memory, String, std::sync::Arc<NamingTables>)>,
    /// Persistent source-point index, consulted only while printing. Older
    /// loop heads must not lose their name when the recent display fills up.
    recorded_states: Option<crate::surface::RecordedStates>,
    source_names: HashMap<Variable, String>,
    /// Exact structural reads held by source locals or recorded states.
    source_read_names: HashMap<MachineTerm, String>,
    source_types: HashMap<Variable, crate::kernel::ProgramType>,
    anonymous_names: HashMap<Variable, String>,
    /// Memories a source spelling names only by a report-local `<state A>`,
    /// defined after the report.
    unknown_states: Vec<Memory>,
    /// Addresses a source spelling names only by a report-local
    /// `<pointer A>`.
    unnamed_pointers: HashMap<Pointer, String>,
    /// Addresses no structural spelling names, spelled as the pointer local
    /// that held them at a recorded state: `at(region(2).exit, p)`.
    recorded_pointers: HashMap<Pointer, String>,
    /// Typed values a recorded state names that the current state no
    /// longer holds: a call's result, `<region>.result`. A range over one is
    /// spelled from that name.
    recorded_values: Vec<(String, crate::kernel::ProgramValue)>,
    /// Source names of mathematical `Integer` variables. Kept apart from
    /// `source_names` because the kernel numbers `Integer` variables
    /// separately from machine ones.
    integer_names: HashMap<Variable, String>,
    /// The parameters or locals a diagnostic spells addresses through, with
    /// their values, when the caller has them.
    naming: Option<std::sync::Arc<NamingTables>>,
}

/// The word a narrow value widened into 32 bits has (rule K8, a relation): a local
/// or parameter holding a promoted value is named, and typed, as the word
/// it holds, as it was when promotion reused the word. Only the widening is
/// read through; a σ keeps its own node.
fn widened_word(term: &MachineTerm) -> &MachineTerm {
    match term.narrow_widening32_operand() {
        Some((_, word)) => word,
        None => term,
    }
}

/// The binder a parameter's value is, if it is one: a scalar's variable, or
/// a `Bool` binder carried as its cast (Stage 5).
fn value_binder(term: &MachineTerm) -> Option<Variable> {
    match widened_word(term) {
        MachineTerm::Variable(variable) => Some(*variable),
        MachineTerm::BoolCast { value, .. } => match value.as_ref() {
            crate::kernel::ConditionTerm::Variable(variable) => Some(*variable),
            _ => None,
        },
        _ => None,
    }
}

impl MemoryStateLabels {
    pub(crate) fn source_type(
        &mut self,
        variable: Variable,
        interface_type: crate::kernel::ProgramType,
    ) {
        self.source_types.insert(variable, interface_type);
    }
    pub(crate) fn source_value_type(&mut self, value: &crate::kernel::ProgramValue) {
        if let crate::kernel::arithmetic_c_value!(term) = value
            && let MachineTerm::Variable(variable) = widened_word(term)
        {
            self.source_type(*variable, value.program_type());
        }
    }

    /// Names the value a function outcome returns `result`, the one spelling
    /// an `ensures` clause has for it, where nothing else spells it: a name
    /// already registered, a read (`old(g[0])`), a model field, or an
    /// address's structural spelling (`&q[1]`) says more. Only the returned
    /// value itself is named; a part of it keeps its own spelling.
    pub(crate) fn source_result(&mut self, value: &crate::kernel::ProgramValue) {
        self.source_value_type(value);
        match value {
            crate::kernel::arithmetic_c_value!(MachineTerm::Variable(variable))
                if crate::kernel::registered_load_for_variable(variable).is_none()
                    && crate::kernel::model_fields::model_field_spelling(*variable).is_none() =>
            {
                self.source_name(*variable, "result".into());
            }
            crate::kernel::ProgramValue::Pointer(pointer) => {
                // A reference result's carrier is the address of `result`.
                let name = if crate::surface::diagnostics::reference_result_source() {
                    "&result"
                } else {
                    "result"
                };
                self.fallback_pointer_name(pointer.pointer(), name.into());
            }
            _ => {}
        }
    }

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
    pub(crate) fn naming(parameter_binding: ParameterBinding<'_>) -> Self {
        let mut labels = Self::default();
        for (parameter, argument) in parameter_binding
            .parameters
            .iter()
            .zip(parameter_binding.arguments)
        {
            let crate::kernel::ProgramExpression::Value(value) = argument else {
                continue;
            };
            if let crate::kernel::ProgramValue::Pointer(pointer) = value {
                labels.immutable_pointer_name(pointer.pointer(), parameter.name());
            }
            let term = match value.numeric_value() {
                crate::kernel::ProgramValue::Bool(term)
                | crate::kernel::ProgramValue::Int8(term)
                | crate::kernel::ProgramValue::Int16(term)
                | crate::kernel::ProgramValue::Int32(term)
                | crate::kernel::ProgramValue::UInt8(term)
                | crate::kernel::ProgramValue::UInt16(term)
                | crate::kernel::ProgramValue::UInt32(term)
                | crate::kernel::ProgramValue::Int64(term)
                | crate::kernel::ProgramValue::UInt64(term)
                | crate::kernel::ProgramValue::Float32(term)
                | crate::kernel::ProgramValue::Float64(term) => term,
                _ => continue,
            };
            if matches!(widened_word(term), MachineTerm::MemoryLoad(..)) {
                labels
                    .source_read_names
                    .entry(widened_word(term).clone())
                    .or_insert_with(|| {
                        crate::surface::diagnostics::rust_variable_spelling(parameter.name())
                            .unwrap_or_else(|| parameter.name().to_string())
                    });
            }
            if let Some(variable) = value_binder(term) {
                let variable = &variable;
                labels.source_name(
                    *variable,
                    crate::surface::diagnostics::rust_variable_spelling(parameter.name())
                        .unwrap_or_else(|| parameter.name().to_string()),
                );
                labels.source_types.insert(*variable, value.program_type());
            }
        }
        labels.naming = Some(std::sync::Arc::new((
            parameter_binding.parameters.to_vec(),
            parameter_binding.arguments.to_vec(),
        )));
        labels.register_ambient_entry();
        labels
    }

    /// A read of the verified function's entry memory spells as `old(...)`,
    /// against the parameters' entry values.
    fn register_ambient_entry(&mut self) {
        let Some((memory, tables)) = AMBIENT_ENTRY.with(|entry| entry.borrow().clone()) else {
            return;
        };
        if self.source_memories.len() < MAX_MEMORY_STATE_LABELS
            && !self
                .source_memories
                .iter()
                .any(|(_, point, _)| point == ENTRY_POINT)
        {
            self.source_memories
                .push((memory, ENTRY_POINT.into(), tables));
        }
    }

    /// A memory as a phrase: `this state`, `function entry`, a recorded
    /// point, or a report-local `<state A>`.
    pub(crate) fn state_phrase(&mut self, memory: &Memory) -> String {
        match self
            .source_memory_context(memory)
            .map(|(point, _)| point.to_owned())
        {
            Some(point) if point == "current" => "this state".into(),
            Some(point) if point == ENTRY_POINT => "function entry".into(),
            Some(point) => format!("`{point}`"),
            None => self.state_label(memory),
        }
    }

    /// The report-local name of a memory no recorded state names.
    pub(crate) fn state_label(&mut self, memory: &Memory) -> String {
        if let Some(index) = self
            .unknown_states
            .iter()
            .position(|known| known.same_storage_roots(memory) || known == memory)
        {
            return format!("<state {}>", alphabetic_label(index));
        }
        if self.unknown_states.len() >= MAX_MEMORY_STATE_LABELS {
            return "<another state>".into();
        }
        self.unknown_states.push(memory.clone());
        format!(
            "<state {}>",
            alphabetic_label(self.unknown_states.len() - 1)
        )
    }

    /// An address no structural spelling names: the pointer local that held
    /// it at a recorded state when one did, otherwise a report-local
    /// `<pointer A>`.
    pub(crate) fn unnamed_pointer(&mut self, pointer: &Pointer) -> String {
        if let Some(name) = self.recorded_pointers.get(pointer) {
            return name.clone();
        }
        self.placeholder_pointer(pointer)
    }

    /// The name [`Self::unnamed_pointer`] falls back to before its
    /// placeholder, when one was registered.
    pub(crate) fn state_pointer_name(&self, pointer: &Pointer) -> Option<&str> {
        self.recorded_pointers.get(pointer).map(String::as_str)
    }

    /// A name for a pointer into `pointer`'s block at offset zero, when a
    /// local held one at the current state or at a recorded state: the
    /// base an address inside an allocation is spelled from. The current
    /// state's locals are preferred, then the shortest state name, so the
    /// choice does not depend on map order.
    pub(crate) fn block_base_name(&self, pointer: &Pointer) -> Option<&str> {
        fn shortest<'a>(names: &'a HashMap<Pointer, String>, pointer: &Pointer) -> Option<&'a str> {
            names
                .iter()
                .filter(|(base, _)| {
                    base.block == pointer.block && base.offset == PointerOffsetTerm::Constant(0)
                })
                .map(|(_, name)| name.as_str())
                .min_by(|left, right| left.len().cmp(&right.len()).then(left.cmp(right)))
        }
        shortest(&self.pointer_sources, pointer)
            .or_else(|| shortest(&self.recorded_pointers, pointer))
    }

    /// A report-local `<pointer A>`, whatever else names the address.
    pub(crate) fn placeholder_pointer(&mut self, pointer: &Pointer) -> String {
        let next = self.unnamed_pointers.len();
        if next >= 128 && !self.unnamed_pointers.contains_key(pointer) {
            return "<another pointer>".into();
        }
        self.unnamed_pointers
            .entry(pointer.clone())
            .or_insert_with(|| format!("<pointer {}>", alphabetic_label(next)))
            .clone()
    }

    /// Current locals take precedence over entry values. This is diagnostic
    /// data only; no proof decision consults these names.
    pub(crate) fn with_state(
        parameter_binding: ParameterBinding<'_>,
        state: &ExecutionState,
    ) -> Self {
        let mut labels = Self::naming(parameter_binding);
        labels.register_current_state(state);
        labels
    }

    /// Restore the selected proof's source bindings after the verifier thread
    /// has unwound. Current-state registration below still distinguishes a
    /// reassigned parameter from its entry value.
    pub(crate) fn register_naming(&mut self, binding: ParameterBinding<'_>) {
        let names = Self::naming(binding);
        self.pointer_sources.extend(names.pointer_sources);
        self.source_names.extend(names.source_names);
        self.source_read_names.extend(names.source_read_names);
        self.source_types.extend(names.source_types);
        if self.naming.is_none() {
            self.naming = names.naming;
        }
    }

    pub(crate) fn register_current_state(&mut self, state: &ExecutionState) {
        let (names, values) = crate::surface::diagnostics::local_naming_tables(state);
        let current = Self::naming(ParameterBinding::new(&names, &values));
        // A reassigned parameter's entry value is not its current value.
        for (variable, name) in &mut self.source_names {
            if names.iter().any(|local| local.name() == name)
                && !current.source_names.contains_key(variable)
            {
                *name = format!("old({name})");
            }
        }
        for (read, name) in &mut self.source_read_names {
            if names.iter().any(|local| local.name() == name)
                && !current.source_read_names.contains_key(read)
            {
                *name = format!("old({name})");
            }
        }
        for (pointer, name) in &mut self.pointer_sources {
            if names.iter().any(|local| local.name() == name)
                && !current.pointer_sources.contains_key(pointer)
            {
                *name = format!("old({name})");
            }
        }
        for (pointer, name) in current.pointer_sources {
            self.pointer_sources.entry(pointer).or_insert(name);
        }
        for (read, name) in current.source_read_names {
            self.source_read_names.entry(read).or_insert(name);
        }
        self.source_types.extend(current.source_types);
        for (variable, name) in current.source_names {
            self.source_names.entry(variable).or_insert(name);
        }
        // Names the state no longer holds -- a parameter after its frame
        // ended, say -- still spell the addresses they held.
        let mut merged = current.naming.as_deref().cloned().unwrap_or_default();
        if let Some(previous) = self.naming.as_deref() {
            for (parameter, argument) in previous.0.iter().zip(&previous.1) {
                if !merged
                    .0
                    .iter()
                    .any(|known| known.name() == parameter.name())
                {
                    merged.0.push(parameter.clone());
                    merged.1.push(argument.clone());
                }
            }
        }
        let merged = std::sync::Arc::new(merged);
        self.naming = Some(merged.clone());
        if self.source_memories.len() < MAX_MEMORY_STATE_LABELS {
            self.source_memories
                .push((state.memory().clone(), "current".into(), merged));
        }
    }

    pub(in crate::surface) fn recorded_states(
        &mut self,
        retained_states: &crate::surface::RecordedStates,
    ) {
        self.recorded_states = Some(retained_states.clone());
    }

    fn recorded_memory_point(&self, memory: &Memory) -> Option<String> {
        let memory = crate::kernel::intern_memory_ref(memory);
        let (selector, _) = self
            .recorded_states
            .as_ref()?
            .point_reading_memory(&memory)?;
        Some(crate::surface::diagnostics::describe_program_point_selector(selector))
    }

    pub(crate) fn source_state(&mut self, state: &ExecutionState, point: String) {
        if self.source_memories.len() < MAX_MEMORY_STATE_LABELS {
            let tables = crate::surface::diagnostics::local_naming_tables(state);
            self.source_memories
                .push((state.memory().clone(), point, std::sync::Arc::new(tables)));
        }
    }

    fn source_memory_context(&self, memory: &Memory) -> Option<(&str, &NamingTables)> {
        // Exact storage roots identify a state without walking memory. When
        // one memory is both the current state and another recorded one,
        // the unqualified current spelling wins.
        let mut found = None;
        for (known, point, naming) in &self.source_memories {
            if known.same_storage_roots(memory) {
                if point == "current" {
                    return Some((point.as_str(), naming.as_ref()));
                }
                found.get_or_insert((point.as_str(), naming.as_ref()));
            }
        }
        if found.is_none() && is_entry_memory(memory) {
            // The memory every execution starts from, or that memory with
            // its cells only named, holds the entry values.
            let naming = self
                .source_memories
                .iter()
                .find(|(_, point, _)| point == ENTRY_POINT)
                .map(|(_, _, naming)| naming.as_ref())
                .or(self.naming.as_deref())?;
            return Some((ENTRY_POINT, naming));
        }
        found
    }

    /// Labels naming what the function being verified declares, when one is.
    pub(crate) fn ambient() -> Self {
        let Some(tables) = AMBIENT_NAMING.with(|naming| naming.borrow().clone()) else {
            return Self::default();
        };
        let mut labels = Self::naming(ParameterBinding::new(&tables.0, &tables.1));
        labels.naming = Some(tables);
        labels
    }

    /// The definitions of the report-local states a source spelling used.
    fn state_legend(&mut self) -> String {
        if self.unknown_states.is_empty() {
            return String::new();
        }
        let states = self.unknown_states.clone();
        let mut output = String::from("\n  where");
        for (index, memory) in states.iter().enumerate() {
            output.push_str(&format!(
                "\n    <state {}> is {}",
                alphabetic_label(index),
                self.describe_state(memory)
            ));
        }
        output
    }

    /// One state in source terms: the program event that produced it.
    fn describe_state(&mut self, memory: &Memory) -> String {
        use crate::kernel::{MemoryConstructionKind, MemoryDerivation};
        if !matches!(
            memory.diagnostic_construction(),
            Some(MemoryConstructionKind::Transform {
                operation: "project memory for pointer read",
                ..
            })
        ) && let Some(point) = self.recorded_memory_point(memory)
        {
            return format!("the program bytes recorded at `{point}`");
        }
        if memory.diagnostic_construction().is_none() && memory.is_initial_diagnostic_memory() {
            return "the memory before the function runs".into();
        }
        let edge = match memory.diagnostic_construction() {
            Some(MemoryConstructionKind::Transition(edge)) => edge.clone(),
            // A read's projection holds that read's value as its one source
            // does, so the program event that produced it is the source's.
            // The source is an earlier memory, so this ends.
            Some(MemoryConstructionKind::Transform {
                operation: "project memory for pointer read",
                sources,
                ..
            }) if sources.len() == 1 => {
                let source = sources[0].clone();
                let described = match self
                    .source_memory_context(&source)
                    .map(|(point, _)| point.to_owned())
                {
                    Some(point) if point == "current" => "this state".into(),
                    Some(point) if point == ENTRY_POINT => "function entry".into(),
                    Some(point) => format!("`{point}`"),
                    None => self.describe_state(&source),
                };
                // The projection's construction can retain a binder from the
                // producer's quantifier, outside the displayed leaf's scope.
                // The leaf names its read; this annotation identifies only
                // the source state, without leaking that internal binder.
                return format!("{described}, projected for one read");
            }
            Some(MemoryConstructionKind::Transform { .. }) => {
                return "a memory derived from another state for one read".into();
            }
            None => match crate::kernel::intern_memory_ref(memory).derivation() {
                Some(edge) => edge,
                None => return "an intermediate memory".into(),
            },
        };
        let tables = self.naming.clone();
        let (parameters, arguments) = tables
            .as_deref()
            .map_or((&[][..], &[][..]), |(p, a)| (p.as_slice(), a.as_slice()));
        let binding = ParameterBinding::new(parameters, arguments);
        match edge.as_ref() {
            MemoryDerivation::Store { pointer, .. } => {
                match crate::surface::diagnostics::diagnostic_source_cell(pointer, binding) {
                    Some(cell) => format!("the memory after the store to `{cell}`"),
                    None => "the memory after a store".into(),
                }
            }
            MemoryDerivation::BranchJoin { .. } => "the memory where branches join".into(),
            MemoryDerivation::CellsForgotten { .. } => {
                "the memory after cached cells were forgotten".into()
            }
            MemoryDerivation::CallHavoc { .. } => "the memory after a call".into(),
            MemoryDerivation::LoopHavoc { .. } => "the memory a loop may have changed".into(),
            MemoryDerivation::BlockDeclared { .. } => {
                "the memory after a local was declared".into()
            }
            MemoryDerivation::LocalLifetimeEnded { .. } => {
                "the memory after a local's lifetime ended".into()
            }
            MemoryDerivation::HeapAllocated { .. } => "the memory after an allocation".into(),
            MemoryDerivation::HeapFreed { .. } => "the memory after a `free`".into(),
            MemoryDerivation::CellsSeeded { .. } => {
                "the memory before the function runs, with its cells named".into()
            }
            _ => format!("the memory after a `{}` step", edge.kind_name()),
        }
    }

    pub(crate) fn naming_tables(
        &self,
    ) -> Option<(
        &[crate::languages::interface::ImportedParameter],
        &[crate::kernel::ProgramExpression],
    )> {
        self.naming
            .as_ref()
            .map(|tables| (tables.0.as_slice(), tables.1.as_slice()))
    }

    pub(crate) fn source_name(&mut self, variable: Variable, name: String) {
        self.source_names.entry(variable).or_insert(name);
    }

    /// An explicit proof binding takes precedence over a compiler temporary.
    pub(crate) fn immutable_source_name(&mut self, variable: Variable, name: String) {
        self.source_names.insert(variable, name);
    }

    /// Names the `Integer` variable `variable` with `name`, when nothing named
    /// it yet.
    pub(crate) fn integer_source_name(&mut self, variable: Variable, name: String) {
        self.integer_names.entry(variable).or_insert(name);
    }

    fn integer_name_for(&self, variable: Variable) -> Option<&str> {
        self.integer_names
            .get(&variable)
            .map(String::as_str)
            .filter(|name| name.len() <= 256)
    }

    /// Spells `pointer` as `name` where no structural spelling names it, when
    /// nothing named it that way yet.
    pub(crate) fn fallback_pointer_name(&mut self, pointer: &Pointer, name: String) {
        if self.recorded_pointers.len() < 128 {
            self.recorded_pointers
                .entry(pointer.clone())
                .or_insert(name);
        }
    }

    /// Records `value` under `name` for spellings that need a typed value,
    /// a memory range's base, when nothing current names it.
    pub(crate) fn fallback_value_name(&mut self, name: String, value: crate::kernel::ProgramValue) {
        if self.recorded_values.len() < 128 && !self.recorded_values.iter().any(|(n, _)| n == &name)
        {
            self.recorded_values.push((name, value));
        }
    }

    /// The naming tables extended by the typed state values.
    pub(crate) fn naming_with_state_values(
        &self,
    ) -> (
        Vec<crate::languages::interface::ImportedParameter>,
        Vec<crate::kernel::ProgramExpression>,
    ) {
        let (mut parameters, mut arguments) = self
            .naming
            .as_deref()
            .map(|tables| (tables.0.clone(), tables.1.clone()))
            .unwrap_or_default();
        let (more_parameters, more_arguments) = crate::surface::diagnostics::value_naming_tables(
            &self.recorded_values.iter().cloned().collect(),
        );
        parameters.extend(more_parameters);
        arguments.extend(more_arguments);
        (parameters, arguments)
    }

    /// Whether a read of `memory` is qualified by a recorded point rather
    /// than a report-local `<state A>`.
    pub(crate) fn names_memory(&self, memory: &Memory) -> bool {
        self.source_memory_context(memory).is_some()
    }

    /// Names `variable` with `name` and its C type when nothing named it yet.
    pub(crate) fn fallback_source_name(
        &mut self,
        variable: Variable,
        name: String,
        interface_type: crate::kernel::ProgramType,
    ) {
        if let std::collections::hash_map::Entry::Vacant(entry) = self.source_names.entry(variable)
        {
            entry.insert(name);
            self.source_types.entry(variable).or_insert(interface_type);
        }
    }

    pub(crate) fn fallback_read_name(&mut self, read: &MachineTerm, name: String) {
        self.source_read_names.entry(read.clone()).or_insert(name);
    }

    fn source_read_name_for(&self, read: &MachineTerm) -> Option<&str> {
        self.source_read_names
            .get(read)
            .map(String::as_str)
            .filter(|name| name.len() <= 256)
    }

    /// Whether some variable is spelled `name` in source, so a printed
    /// binder must not take it.
    fn names_a_variable(&self, name: &str) -> bool {
        self.source_names.values().any(|source| source == name)
            || self.source_read_names.values().any(|source| source == name)
            || self.integer_names.values().any(|source| source == name)
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
    fn label(&mut self, memory: &Memory) -> Option<usize> {
        if let Some(index) = self.memory_identities.get(&memory.diagnostic_identity()) {
            return Some(*index);
        }
        if let Some(index) = self
            .memories
            .iter()
            .take(MAX_MEMORY_STATE_LABELS)
            .position(|labeled| labeled.same_storage_roots(memory) || labeled == memory)
        {
            return Some(index + 1);
        }
        let limit = if self.trace_labels {
            MAX_NODES
        } else {
            MAX_MEMORY_STATE_LABELS
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

    pub(crate) fn memory_state_name(&mut self, memory: &Memory) -> String {
        self.label(memory).map_or_else(
            || "state<untracked>".to_owned(),
            |index| format!("state#{index}"),
        )
    }
}

/// Exact Click spelling for a bounded fact whose operands are named source
/// values. Historical reads require their own recorded state's names and an
/// explicit `at(...)`; unknown states and generated values do not qualify.
#[cfg(test)]
pub(crate) fn render_simple_click_fact_labeled(
    proposition: &Proposition,
    labels: &mut MemoryStateLabels,
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
pub(crate) fn render_read_resolution(
    resolution: &crate::kernel::ReadResolutionDiagnostic,
    labels: &mut MemoryStateLabels,
) -> String {
    let _typed = TypedNotationScope::enter();
    let query = render_proposition_labeled(
        &Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(resolution.read.clone()),
                right: Box::new(resolution.expected.clone()),
            },
            true,
        ),
        labels,
    );
    let producer = labels.memory_state_name(resolution.producer.memory());
    let stopped = resolution
        .stopped_at
        .as_ref()
        .map(|memory| labels.memory_state_name(memory.memory()));
    let mut result = format!(
        "read-resolution check:\n    checked read equality: {query}\n    producer source: {producer}\n    walk stop: {}{}",
        stopped.map(|at| format!("{at}: ")).unwrap_or_default(),
        resolution.reason
    );
    if let Some(value) = &resolution.recovered {
        let equality = render_proposition_labeled(
            &Proposition::Equal(
                Term::ProgramValue(value.clone()),
                Term::ProgramValue(crate::kernel::ProgramValue::UInt64(
                    resolution.expected.clone(),
                )),
            ),
            labels,
        );
        result.push_str(&format!(
            "\n    recovered word equality: {equality}\n    equality check: {}",
            if resolution.equal {
                "proved"
            } else {
                "not proved"
            }
        ));
    } else {
        result.push_str("\n    recovered value: none\n    equality check: not attempted (no complete word recovered)");
    }
    result
}

pub(crate) fn render_transport_cell_walk(
    walk: &crate::kernel::TransportCellWalkDiagnostic,
    labels: &mut MemoryStateLabels,
) -> String {
    let _typed = TypedNotationScope::enter();
    let pointer = labels.pointer_value_name(&walk.pointer);
    let start = labels.memory_state_name(walk.start.memory());
    let stop = labels.memory_state_name(walk.stopped_at.memory());
    format!(
        "address: {pointer}; width: {} bytes; start: {start}; stop: {stop}: {}; crossed: {} steps; extended bridging: {}; explicit DAG check: {}",
        walk.bytes, walk.reason, walk.crossed, walk.extended, walk.explicit,
    )
}

/// One cell's address as a report names it: its source spelling when the
/// report's names give one, and otherwise its labelled address.
pub(crate) fn render_cell_address(pointer: &Pointer, labels: &mut MemoryStateLabels) -> String {
    let naming = labels.naming.clone();
    let (parameters, arguments) = naming
        .as_deref()
        .map_or((&[][..], &[][..]), |(p, a)| (p.as_slice(), a.as_slice()));
    crate::surface::diagnostics::diagnostic_source_cell(
        pointer,
        ParameterBinding::new(parameters, arguments),
    )
    .map(|source| format!("`{source}`"))
    .unwrap_or_else(|| {
        if typed_notation() {
            format!("address {}", labels.pointer_value_name(pointer))
        } else {
            format!("address `{}`", labels.unnamed_pointer(pointer))
        }
    })
}

pub(crate) fn render_memory_history_check(
    history: &super::MemoryHistoryDiagnostic,
    labels: &mut MemoryStateLabels,
) -> Option<String> {
    use crate::kernel::resource_tracker::{Change, OwnedResource};
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
    let written = render_cell_address(written, labels);
    let read = render_cell_address(read, labels);
    let memory = at.shared_memory().memory();
    let retained_state = if typed_notation() {
        labels.memory_state_name(memory)
    } else {
        labels.state_phrase(memory)
    };
    let miss = history
        .store_search_miss
        .as_ref()
        .map(|miss| {
            format!(
                "\n    store search: {}",
                crate::surface::diagnostics::describe_store_separation_miss(
                    &miss.statement,
                    miss.cell.as_deref(),
                    &miss.fact,
                )
            )
        })
        .unwrap_or_default();
    Some(format!(
        "memory history without the failed check's facts stops at {retained_state}:\n    store: {} bytes at {written}\n    read range checked: {bytes} bytes at {read}{miss}\n    supplemental history explanation: equality and ownership facts from the failed check are not used by this walk, so a store the check itself crosses (by a quantified fact's guard, for one) can stop it; it does not say why the check failed",
        written_bytes,
    ))
}

/// Render one proposition without allowing its shape or attached states to
/// determine the size of the error message.
pub(crate) fn render_proposition(proposition: &Proposition) -> String {
    let mut labels = MemoryStateLabels::ambient();
    let mut text = render_proposition_labeled(proposition, &mut labels);
    text.push_str(&labels.trace_legend());
    text
}

type NamingTables = (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<crate::kernel::ProgramExpression>,
);

/// Shared entry naming captured without walking parameters or memory. The
/// terminal proof state takes precedence; this preserves ambient names when
/// a search-only error is rendered after the verification session unwinds.
#[derive(Clone, Default)]
pub(crate) struct CapturedNaming(Option<(Memory, std::sync::Arc<NamingTables>)>);

impl std::fmt::Debug for CapturedNaming {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CapturedNaming")
            .field("present", &self.0.is_some())
            .finish()
    }
}

impl PartialEq for CapturedNaming {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some((_, left)), Some((_, right))) => std::sync::Arc::ptr_eq(left, right),
            _ => false,
        }
    }
}

impl Eq for CapturedNaming {}

impl CapturedNaming {
    pub(crate) fn capture() -> Self {
        Self(AMBIENT_ENTRY.with(|entry| entry.borrow().clone()))
    }

    pub(crate) fn register_if_missing(&self, labels: &mut MemoryStateLabels) {
        if labels.naming.is_some() {
            return;
        }
        let Some((memory, tables)) = &self.0 else {
            return;
        };
        labels.register_naming(ParameterBinding::new(&tables.0, &tables.1));
        labels.naming = Some(tables.clone());
        if labels.source_memories.len() < MAX_MEMORY_STATE_LABELS
            && !labels
                .source_memories
                .iter()
                .any(|(_, point, _)| point == ENTRY_POINT)
        {
            labels
                .source_memories
                .push((memory.clone(), ENTRY_POINT.into(), tables.clone()));
        }
    }
}

/// Whether `memory` is the initial memory, or it with cells seeded from it:
/// either holds exactly the values memory had before the code ran. A bounded
/// walk, done only while printing a failure.
fn is_entry_memory(memory: &Memory) -> bool {
    let mut current = memory.clone();
    for _ in 0..8 {
        if current.is_initial_diagnostic_memory() {
            return true;
        }
        let edge = match current.diagnostic_construction() {
            Some(crate::kernel::MemoryConstructionKind::Transition(edge)) => edge.clone(),
            Some(_) => return false,
            None => match crate::kernel::intern_memory_ref(&current).derivation() {
                Some(edge) => edge,
                None => return false,
            },
        };
        let crate::kernel::MemoryDerivation::CellsSeeded { base, .. } = edge.as_ref() else {
            return false;
        };
        current = base.memory().clone();
    }
    false
}

/// The recorded point a read of the function's entry memory names; it
/// spells as `old(...)`.
pub(crate) const ENTRY_POINT: &str = "function.entry";

thread_local! {
    /// The parameters of the C function being verified and their entry
    /// values. Diagnostics only: nothing reads it to decide a proof.
    static AMBIENT_NAMING: std::cell::RefCell<Option<std::sync::Arc<NamingTables>>> =
        const { std::cell::RefCell::new(None) };
    /// That function's entry memory, so a read of it spells as `old(...)`.
    /// One retained handle per verified function; diagnostics only.
    static AMBIENT_ENTRY: std::cell::RefCell<Option<(Memory, std::sync::Arc<NamingTables>)>> =
        const { std::cell::RefCell::new(None) };
    /// Set while a `--trace-proof` trace is rendered: traces keep their
    /// typed notation, which names each read's width and state.
    static TYPED_NOTATION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Starts verifying a C function whose parameters hold `arguments` in the
/// memory `entry`.
pub(crate) fn enter_ambient_naming(parameter_binding: ParameterBinding<'_>, entry: &Memory) {
    let tables = std::sync::Arc::new((
        parameter_binding.parameters.to_vec(),
        parameter_binding.arguments.to_vec(),
    ));
    AMBIENT_NAMING.with(|naming| *naming.borrow_mut() = Some(tables.clone()));
    AMBIENT_ENTRY.with(|slot| *slot.borrow_mut() = Some((entry.clone(), tables)));
}

pub(crate) fn clear_ambient_naming() {
    AMBIENT_NAMING.with(|naming| *naming.borrow_mut() = None);
    AMBIENT_ENTRY.with(|slot| *slot.borrow_mut() = None);
    crate::surface::diagnostics::clear_ambient_object_fields();
}

/// The source declaration supplies nominal layout metadata even when a
/// diagnostic's current-state naming table contains only kernel types.
pub(in crate::surface) fn ambient_source_parameter(
    name: &str,
) -> Option<crate::languages::interface::ImportedParameter> {
    AMBIENT_NAMING.with(|slot| {
        slot.borrow()
            .as_ref()?
            .0
            .iter()
            .find(|parameter| parameter.name() == name)
            .cloned()
    })
}

/// While alive, propositions render in the typed trace notation.
pub(crate) struct TypedNotationScope(bool);

impl TypedNotationScope {
    pub(crate) fn enter() -> Self {
        Self(TYPED_NOTATION.with(|typed| typed.replace(true)))
    }
}

impl Drop for TypedNotationScope {
    fn drop(&mut self) {
        TYPED_NOTATION.with(|typed| typed.set(self.0));
    }
}

fn typed_notation() -> bool {
    TYPED_NOTATION.with(std::cell::Cell::get)
}

/// A bounded view of one exact resource representation for a proof trace.
#[cfg(test)]
pub(crate) fn render_resource_fact(fact: &ResourceFact) -> String {
    let mut labels = MemoryStateLabels::default();
    render_resource_fact_labeled(fact, &mut labels)
}

pub(crate) fn render_resource_fact_labeled(
    fact: &ResourceFact,
    labels: &mut MemoryStateLabels,
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
        ResourceFact::Own(resource, quantity) => {
            renderer.push("owns ");
            renderer.resource(resource);
            renderer.push(" x ");
            renderer.bitvector(quantity);
        }
        ResourceFact::View(resource) => {
            renderer.push("views ");
            renderer.resource(resource);
        }
    }
    if renderer.truncated {
        renderer.output.push('…');
    }
    renderer.output
}

/// Resource facts follow the same source/typed policy as propositions.
pub(crate) fn render_resource_fact_spelled(
    fact: &ResourceFact,
    labels: &mut MemoryStateLabels,
) -> String {
    if typed_notation() {
        render_resource_fact_labeled(fact, labels)
    } else {
        surface::source_resource_fact(fact, labels)
    }
}

pub(in crate::surface) fn render_resource_fact_diagnostic(
    fact: &ResourceFact,
    binding: ParameterBinding<'_>,
) -> String {
    let mut labels = MemoryStateLabels::naming(binding);
    let mut text = render_resource_fact_spelled(fact, &mut labels);
    text.push_str(&labels.trace_legend());
    text
}

pub(in crate::surface) fn render_resource_facts_diagnostic(
    facts: &[ResourceFact],
    binding: ParameterBinding<'_>,
) -> String {
    let mut labels = MemoryStateLabels::naming(binding);
    let mut text = crate::surface::diagnostics::describe_bounded_list(facts, |fact| {
        render_resource_fact_spelled(fact, &mut labels)
    });
    text.push_str(&labels.trace_legend());
    text
}

/// A resource list spelled with the report's own label set and no legend, so
/// a placeholder in a hidden record (`record { first.v: <unnamed A> }`) is the
/// same value the report's pure facts call `<unnamed A>`. The caller appends
/// the shared legend once.
pub(in crate::surface) fn render_resource_facts_labeled(
    facts: &[ResourceFact],
    labels: &mut MemoryStateLabels,
) -> String {
    crate::surface::diagnostics::describe_bounded_list(facts, |fact| {
        render_resource_fact_spelled(fact, labels)
    })
}

/// One instance of `name` with its hidden record in the source spelling a
/// resource list uses, `pair(p) record { first.v: <unnamed A> }`; `None` when
/// the schema is a resource's own declared fields.
pub(in crate::surface) fn render_hidden_record_instance_labeled(
    name: &str,
    arguments: &[crate::kernel::AlgebraicValue],
    schema: &[(String, crate::kernel::ResourceFieldType)],
    fields: &[crate::kernel::AlgebraicValue],
    labels: &mut MemoryStateLabels,
) -> Option<String> {
    let record = surface::source_hidden_record(schema, fields, labels)?;
    let application = surface::source_resource(
        &crate::kernel::Resource::Composite {
            name: name.to_owned(),
            arguments: arguments.into(),
        },
        labels,
    );
    Some(format!("{application} {record}"))
}

pub(in crate::surface) fn render_resource_diagnostic(
    resource: &Resource,
    binding: ParameterBinding<'_>,
) -> String {
    let mut labels = MemoryStateLabels::naming(binding);
    let mut text = if typed_notation() {
        let fact = render_resource_fact_labeled(&ResourceFact::View(resource.clone()), &mut labels);
        fact.strip_prefix("views ").unwrap_or(&fact).to_owned()
    } else {
        surface::source_resource(resource, &mut labels)
    };
    text.push_str(&labels.trace_legend());
    text
}

/// One proposition display policy for facts, requirements, and goals.
/// Ordinary verifier errors spell every proposition in Click or source
/// syntax (`surface::source`). A `--trace-proof` trace uses source spelling
/// only when it preserves the checked identities; otherwise its typed
/// renderer names each read's width, state, and address with report-local
/// labels.
pub(crate) fn render_proposition_labeled(
    proposition: &Proposition,
    labels: &mut MemoryStateLabels,
) -> String {
    if !typed_notation() {
        return surface::source(proposition, labels);
    }
    labels.trace_labels = true;
    surface::display(proposition, labels)
        .unwrap_or_else(|| render_kernel_fact(proposition, labels, true))
}

/// Lower-level renderer tests exercise the bounded notation directly.
#[cfg(test)]
pub(crate) fn render_internal_proposition_labeled(
    proposition: &Proposition,
    labels: &mut MemoryStateLabels,
) -> String {
    render_kernel_fact(proposition, labels, false)
}

#[cfg(test)]
pub(crate) fn render_trace_fact_labeled(
    proposition: &Proposition,
    labels: &mut MemoryStateLabels,
) -> String {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    render_proposition_labeled(proposition, labels)
}

fn render_kernel_fact(
    proposition: &Proposition,
    labels: &mut MemoryStateLabels,
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
    render_integer_term_labeled(term, &mut MemoryStateLabels::ambient())
}

/// One exact-arithmetic term under the report's labels.
pub(crate) fn render_integer_term_labeled(
    term: &IntegerTerm,
    labels: &mut MemoryStateLabels,
) -> String {
    surface::integer(term, labels)
}

/// One C value in source syntax, under the report's labels.
pub(crate) fn render_program_value_labeled(
    value: &crate::kernel::ProgramValue,
    labels: &mut MemoryStateLabels,
) -> String {
    surface::source_value(value, labels)
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
    let mut labels = MemoryStateLabels::ambient();
    let left = surface::integer(left, &mut labels);
    let right = surface::integer(right, &mut labels);
    format!("{left} {operator} {right}")
}

/// Describe a refused Integer capture: which written subterm carries an
/// evaluation condition, and which condition the proof context is missing.
pub(crate) fn describe_spec_capture_refusal(refusal: &SpecCaptureRefusal) -> String {
    describe_spec_capture_refusal_labeled(refusal, &mut MemoryStateLabels::ambient())
}

pub(crate) fn describe_spec_capture_refusal_labeled(
    refusal: &SpecCaptureRefusal,
    labels: &mut MemoryStateLabels,
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
    labels: &'a mut MemoryStateLabels,
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
                if name == &format!("{}1", crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX)
                    && let [origin, start, end] = arguments.as_slice()
                {
                    self.push("subobject bounds of ");
                    self.term(origin);
                    self.push(" cover bytes [");
                    self.term(start);
                    self.push(", ");
                    self.term(end);
                    self.push(")");
                    self.depth -= 1;
                    return;
                }
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
            Proposition::ForAll {
                var, sort, body, ..
            } => {
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
            Proposition::MemoryLoadable {
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
            Proposition::MemoryCanStore {
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
            Proposition::MemoryReadDefined {
                memory, pointer, ..
            } => {
                self.push("defined-read(");
                self.memory(memory);
                self.push(", ");
                self.pointer(pointer);
                self.push(")");
            }
            Proposition::MemoryLoads {
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
            Proposition::ResourceSeparate { left, right } => {
                self.resource(left);
                self.push(" separate ");
                self.resource(right);
            }
            Proposition::ResourceViewable { memory, resource } => {
                self.push("viewable(");
                self.resource(resource);
                self.push(" in ");
                self.memory(memory);
                self.push(")");
            }
            Proposition::ResourceContains { parent, child } => {
                self.resource(parent);
                self.push(" contains ");
                self.resource(child);
            }
            Proposition::ResourceComposition(context) => self.resource_composition(context),
            Proposition::MemoryMutatesOnly {
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
            Proposition::MemoryEffectSummary {
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
            Proposition::HeapAllocationFreed {
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
                self.bitvector(bytes.bytes());
                self.push(")");
            }
            Proposition::ProgramExpressionEvaluates {
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
            Proposition::ProgramConditionEvaluates {
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
            Proposition::ProgramStatementExecutes {
                state,
                statement: _,
                outcome,
            }
            | Proposition::ProgramStatementVerifies {
                state,
                statement: _,
                outcome,
            } => {
                self.push("statement-");
                self.push(
                    if matches!(proposition, Proposition::ProgramStatementVerifies { .. }) {
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
            Proposition::ProgramFunctionExecutes {
                state,
                function: _,
                arguments,
                outcome,
            }
            | Proposition::ProgramFunctionVerifies {
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
            Proposition::ProgramFunctionSatisfiesSpecification { .. } => {
                self.push("function-satisfies(<C function specification>)")
            }
            Proposition::ProgramFunctionPartiallySatisfiesSpecification { .. } => {
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
            AlgebraicValueType::ObjectPointer(_, class) => {
                self.push(&format!("{}*", class.spelling()))
            }
            AlgebraicValueType::Program(ty) => self.fmt(format_args!("{ty:?}")),
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
            Term::ProgramValue(v) => self.cvalue(v),
            Term::ExpressionOutcome(o) => self.outcome(o),
            Term::StatementOutcome(_) => self.push("statement-outcome(<state state>)"),
            Term::FunctionOutcome(_) => self.push("function-outcome(<state state>)"),
            Term::Memory(m) => self.memory(m),
            Term::ExecutionState(s) => self.state(s),
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
            AlgebraicTermNode::MemoryLoad { memory, pointer } => {
                self.bitvector(&AlgebraicTermNode::memory_load_carrier(memory, pointer))
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
            AlgebraicTermNode::If {
                condition,
                then_term,
                else_term,
            } => {
                self.push("if(");
                self.condition(condition);
                self.push(", ");
                self.algebraic(then_term);
                self.push(", ");
                self.algebraic(else_term);
                self.push(")");
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
            AlgebraicValue::Program(value) => self.cvalue(value),
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
            // Explicit output boundary of the native diagnostic renderer.
            PureFunctionArgument::SharedMachine(value) => {
                self.cvalue(&value.ty().value_from_term(value.structural_value().clone()));
            }
            PureFunctionArgument::Integer(value) => self.integer_shared(value),
            PureFunctionArgument::Algebraic(value) => self.algebraic(value),
            // The state identity is printed, not elided. A goal that
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
                        crate::kernel::program_type_spelling(*element_type)
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
        // Definedness of a partial machine operation is the condition a
        // capture or evaluation refusal most often names, so print the
        // operation instead of a placeholder.
        if let Some((operator, a, b)) = c.as_bitvector_comparison() {
            let symbol = operator.program_symbol();
            if operator.is_overflow() {
                self.overflow_condition_bv(a, b, operator.operand_type(), symbol);
            } else {
                let symbol = if symbol == "==" { "=" } else { symbol };
                self.binary_condition_bv(a, b, &format!("{} {symbol}", operator.operand_type()));
            }
            return;
        }
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
            ConditionTerm::PointerValueEqual(a, b) => {
                self.pointer(a.pointer());
                self.push(" == ");
                self.pointer(b.pointer());
            }
            ConditionTerm::PointerEqual(a, b) => {
                self.pointer(a);
                self.push(" = ");
                self.pointer(b);
            }
            ConditionTerm::BoolApplication(application) => {
                self.push(application.name());
                self.push("(...)");
            }
            ConditionTerm::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => {
                self.push("if ");
                self.condition(condition);
                self.push(" { ");
                self.condition(then_condition);
                self.push(" } else { ");
                self.condition(else_condition);
                self.push(" }");
            }
            ConditionTerm::BoolEqual(a, b) => {
                self.push("bool(");
                self.condition(a);
                self.push(" = ");
                self.condition(b);
                self.push(")");
            }
            ConditionTerm::BoolLoad(memory, pointer) => {
                self.push("read<Bool>(");
                self.memory(memory.as_ref());
                self.push(", pointer=");
                self.pointer(pointer);
                self.push(")");
            }
            _ => self.push("condition(<bounded operation>)"),
        }
    }
    fn binary_condition_bv(&mut self, a: &MachineTerm, b: &MachineTerm, label: &str) {
        // Equality shares one 32-bit kernel form between signed and unsigned
        // C values. Retained type metadata disambiguates a returned value
        // even when it has no source name.
        let unsigned_equality = label == "int32 ="
            && [a, b].iter().any(|value| {
                matches!(value, MachineTerm::Variable(variable)
                if self.labels.source_types.get(variable) == Some(&crate::kernel::ProgramType::UInt32))
            });
        self.push(if unsigned_equality { "uint32 =" } else { label });
        self.push("(");
        let signed = label.starts_with("int32 ") && !unsigned_equality;
        self.comparison_bitvector(a, signed);
        self.push(", ");
        self.comparison_bitvector(b, signed);
        self.push(")");
    }
    fn comparison_bitvector(&mut self, value: &MachineTerm, signed: bool) {
        if signed && let bits32_constant!(value) = value {
            self.fmt(format_args!("{}", constant_u32(*value) as i32));
        } else {
            self.bitvector(value);
        }
    }
    fn overflow_condition_bv(
        &mut self,
        a: &MachineTerm,
        b: &MachineTerm,
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
                    Some(spelling) if self.trace_facts => {
                        let name = self.variable_name(*variable, "integer");
                        self.fmt(format_args!("{name}={spelling}"));
                    }
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
            IntegerTerm::If {
                condition,
                then_term,
                else_term,
            } => {
                self.push("if(");
                self.condition(condition);
                self.push(", ");
                self.integer_shared(then_term);
                self.push(", ");
                self.integer_shared(else_term);
                self.push(")");
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
    fn bitvector(&mut self, v: &MachineTerm) {
        if self.truncated || !self.visit() || self.depth >= MAX_DEPTH {
            self.truncated = true;
            return;
        }
        self.depth += 1;
        // Rule C1: a specification `Bool` travels as its cast to `uint8`,
        // which reads as the `Bool` itself.
        if let MachineTerm::BoolCast { to, value } = v {
            if *to == crate::kernel::MachineIntegerType::UInt8 {
                self.condition(value);
            } else {
                self.push("(");
                self.condition(value);
                self.fmt(format_args!(") as {to:?}"));
            }
            self.depth -= 1;
            return;
        }
        if let MachineTerm::MemoryLoad(retained_state, pointer, kind) = v {
            // `memory` prints its own memory label.
            if self.trace_facts {
                self.fmt(format_args!("read<{}>(", trace_load_kind(*kind)));
            } else {
                self.push("load(");
            }
            self.memory(retained_state.as_ref());
            self.push(", pointer=");
            self.pointer(pointer);
            self.push(")");
            self.depth -= 1;
            return;
        }
        // A registered load variable is a name for one load, and the load it
        // names is the part a reader compares. Printing the bare id made two
        // reads of one address at two states look like two unrelated
        // numbers, and printing only the address made them look identical;
        // neither says which memory each side reads, which is the whole
        // question wherever a load fact fails to carry across a step.
        if let MachineTerm::Variable(variable) = v
            && crate::kernel::is_load_variable(variable)
            && let Some((retained_state, pointer)) =
                crate::kernel::registered_load_for_variable(variable)
        {
            let name = self.variable_name(*variable, "load");
            if self.trace_facts {
                let kind = crate::kernel::registered_load_kind_for_variable(variable)
                    .map(trace_load_kind)
                    .unwrap_or_else(|| "unrecorded type".into());
                self.fmt(format_args!("{name}=read<{kind}>("));
            } else {
                self.fmt(format_args!("{name}=load("));
            }
            self.memory(retained_state.memory());
            self.push(", pointer=");
            self.pointer(&pointer);
            self.push(")");
            self.depth -= 1;
            return;
        }
        match v {
            bits32_constant!(v) => self.fmt(format_args!("{v}", v = constant_u32(*v))),
            int64_constant!(v) => self.fmt(format_args!("{v}i64", v = constant_i64(*v))),
            crate::kernel::native_constant!(format, bits) => {
                let constant =
                    crate::kernel::MachineIntegerConstant::from_term_bits(format.format(), *bits);
                let format = constant.format();
                let sign = if format.is_signed() { 'i' } else { 'u' };
                match constant.to_i128() {
                    Some(value) => self.fmt(format_args!("{value}{sign}{}", format.bits())),
                    None => self.fmt(format_args!("{}{sign}{}", constant.bits(), format.bits())),
                }
            }
            uint64_constant!(v) => self.fmt(format_args!("{v}u64", v = constant_u64(*v))),
            // A model-field variable is a name for one field of one instance,
            // and the field is the part a reader compares. The id is kept
            // beside it here, as a load variable's is, because this renderer
            // prints the kernel's own goal and premises.
            MachineTerm::Variable(v)
                if let Some(spelling) = crate::kernel::model_fields::model_field_spelling(*v) =>
            {
                let name = self.variable_name(*v, "value");
                self.fmt(format_args!("{name}={spelling}"))
            }
            MachineTerm::Variable(v) => {
                let name = self.variable_name(*v, "value");
                self.push(&name);
            }
            binary_term!(Int32, Add, a, b) => self.binary_bv("+", a, b),
            binary_term!(Int32, Subtract, a, b) => self.binary_bv("-", a, b),
            binary_term!(Int32, Multiply, a, b) => self.binary_bv("*", a, b),
            _ if self.machine_operation(v) => {}
            MachineTerm::RangeFold {
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
            MachineTerm::PureFunctionApplication { name, arguments } => {
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
            MachineTerm::ClickFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                self.pure_arguments(arguments);
                self.push(")");
            }
            MachineTerm::AlgebraicMatch { scrutinee, arms } => {
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
            MachineTerm::PointerAddress(pointer, _) => {
                self.push("address(");
                self.pointer(pointer);
                self.push(")");
            }
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                to: destination,
                ..
            } => {
                // A signed byte read renders as the conversion of the byte's
                // unsigned read, which is what it is.
                self.push(&format!("{destination:?}").to_ascii_lowercase());
                self.push("(");
                self.bitvector(value);
                self.push(")");
            }
            _ => self.push("bitvector(<bounded opaque operation>)"),
        }
        self.depth -= 1;
    }
    fn binary_bv(&mut self, op: &str, left: &MachineTerm, right: &MachineTerm) {
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
                self.bitvector(value.structural_value());
                self.fmt(format_args!(")*{byte_width} bytes"));
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                self.push(if *unsigned { "uint64(" } else { "int64(" });
                self.bitvector(value.structural_value());
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
            let spelled = crate::surface::diagnostics::describe_pointer(
                p,
                ParameterBinding::new(parameters, arguments),
            );
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
    fn resource(&mut self, resource: &Resource) {
        match resource {
            Resource::Emp => self.push("separation::emp"),
            Resource::Star(pair) => {
                self.push("(");
                self.resource(&pair.0);
                self.push(" * ");
                self.resource(&pair.1);
                self.push(")");
            }
            Resource::Footprint(fp) => self.push(&fp.source),
            Resource::Parameter(v) => self.push(&format!("resource#{:?}", v)),
            Resource::MutexGuard(identity) => {
                self.push("mutex_guard(");
                self.pointer(identity.mutex());
                self.push(")");
            }
            Resource::MutexLive(identity) => {
                self.push("mutex_live(");
                self.pointer(identity.mutex());
                self.push(")");
            }
            Resource::MutexUse(identity) => {
                self.push("mutex_use(");
                self.pointer(identity.mutex());
                if let Some(ty) = identity.protected_type() {
                    self.push(", ");
                    self.push(ty.family());
                    self.resource_arguments(ty.arguments());
                }
                self.push(")");
            }
            Resource::Publication(right) => {
                self.push(right.side().keyword());
                self.push("(");
                self.pointer(right.flag());
                self.push(", ");
                self.push(right.payload().family());
                self.resource_arguments(right.payload().arguments());
                if let Some(observed) = right.observed() {
                    self.push(", observed=");
                    self.cvalue(observed);
                }
                self.push(")");
            }
            Resource::PopulationAuthority(description) => {
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
            Resource::Memory(range) => {
                let start = self.output.len();
                self.push("memory(");
                self.pointer(range.base());
                self.fmt(format_args!("[{:?}:", range.kind()));
                self.bitvector(range.bound_terms().0);
                self.push("..");
                self.bitvector(range.bound_terms().1);
                self.fmt(format_args!("], stride={})", range.element_width()));
                if !self.truncated {
                    let suffix = self
                        .labels
                        .range_collisions
                        .as_mut()
                        .and_then(|collisions| collisions.observe(&self.output[start..], range));
                    if let Some(suffix) = suffix {
                        self.push(&suffix);
                    }
                }
            }
            Resource::Composite { name, arguments } | Resource::Token { name, arguments } => {
                self.push(name);
                self.resource_arguments(arguments);
            }
            Resource::Instance(instance) => {
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
            Resource::Iterated(iterated) => {
                self.push("iterated-resource(");
                self.push(iterated.owner());
                self.push(", ");
                self.bitvector(iterated.lower());
                self.push("..");
                self.bitvector(iterated.upper());
                let index = Variable(u64::MAX - 7);
                self.bound_names.push((index, "k".into()));
                let guard_range = iterated.guard_range();
                self.fmt(format_args!(", k: guard<{:?}>(", guard_range.kind()));
                self.pointer(iterated.guard().base());
                self.fmt(format_args!("[k], stride={})", guard_range.element_width()));
                self.push(if iterated.guard().holds_when_equal() {
                    " == "
                } else {
                    " != "
                });
                self.bitvector(iterated.guard().value());
                self.push(", element=");
                self.resource(&Resource::Memory(
                    iterated.element_range(&MachineTerm::Variable(index)),
                ));
                self.bound_names.pop();
                self.push(", holes=[");
                for (index, hole) in iterated.holes().iter().enumerate() {
                    if !self.visit() {
                        break;
                    }
                    if index > 0 {
                        self.push(", ");
                    }
                    self.bitvector(hole);
                }
                self.push("])");
            }
        }
    }

    fn memory(&mut self, memory: &Memory) {
        match self.labels.label(memory) {
            Some(label) => self.fmt(format_args!("state#{label}")),
            None => self.push("state<untracked>"),
        }
    }
    fn state(&mut self, state: &ExecutionState) {
        self.push("state(");
        self.memory(state.memory());
        self.push(")");
    }
    fn cvalue(&mut self, value: &crate::kernel::ProgramValue) {
        match value.numeric_value() {
            crate::kernel::ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
            crate::kernel::ProgramValue::Parameter(term) => self.algebraic(term),
            crate::kernel::ProgramValue::Void => self.push("void"),
            crate::kernel::ProgramValue::Bool(v) => {
                self.push("bool(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Int128(v) => {
                self.push("int128(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::UInt128(v) => {
                self.push("uint128(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Int8(v) => {
                self.push("int8(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Int16(v) => {
                self.push("int16(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Int32(v) => {
                self.push("int32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::UInt8(v) => {
                self.push("uint8(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::UInt16(v) => {
                self.push("uint16(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::UInt32(v) => {
                self.push("uint32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Int64(v) => {
                self.push("int64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::UInt64(v) => {
                self.push("uint64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Float32(v) => {
                self.push("float32(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Float64(v) => {
                self.push("float64(");
                self.bitvector(v);
                self.push(")");
            }
            crate::kernel::ProgramValue::Pointer(p) => {
                if self.trace_facts {
                    self.fmt(format_args!(
                        "ptr<{}>(",
                        crate::kernel::program_type_spelling(p.program_type())
                    ));
                    self.pointer(p);
                    self.push(")");
                } else {
                    self.pointer(p);
                }
            }
        }
    }
    fn outcome(&mut self, outcome: &ExpressionOutcome) {
        match outcome {
            ExpressionOutcome::Value(value) => self.cvalue(value),
            ExpressionOutcome::UndefinedBehavior(_) => self.push("undefined-behavior"),
            ExpressionOutcome::RuntimeError(_) => self.push("runtime-error"),
        }
    }
    fn condition_outcome(&mut self, outcome: &crate::kernel::ConditionOutcome) {
        self.push(match outcome {
            crate::kernel::ConditionOutcome::Value(true) => "true",
            crate::kernel::ConditionOutcome::Value(false) => "false",
            crate::kernel::ConditionOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::ConditionOutcome::RuntimeError(_) => "runtime-error",
        });
    }
    fn statement_outcome(&mut self, outcome: &crate::kernel::StatementOutcome) {
        self.push(match outcome {
            crate::kernel::StatementOutcome::Normal(_) => "normal",
            crate::kernel::StatementOutcome::Break(_) => "break",
            crate::kernel::StatementOutcome::Continue(_) => "continue",
            crate::kernel::StatementOutcome::Jump { .. } => "jump",
            crate::kernel::StatementOutcome::Return { .. } => "return",
            crate::kernel::StatementOutcome::Throw { .. } => "throw",
            crate::kernel::StatementOutcome::VerificationDiverges => "verification-diverges",
            crate::kernel::StatementOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::StatementOutcome::RuntimeError(_) => "runtime-error",
        });
    }
    fn function_outcome(&mut self, outcome: &crate::kernel::FunctionOutcome) {
        self.push(match outcome {
            crate::kernel::FunctionOutcome::Return { .. } => "return",
            crate::kernel::FunctionOutcome::Throw { .. } => "throw",
            crate::kernel::FunctionOutcome::VerificationDiverges => "verification-diverges",
            crate::kernel::FunctionOutcome::UndefinedBehavior(_) => "undefined-behavior",
            crate::kernel::FunctionOutcome::RuntimeError(_) => "runtime-error",
        });
    }
}

/// A read's kind as a proof trace spells it. A 32-bit read of either
/// signedness reads one word, which the trace names `Bits32`; its
/// signedness is the reader's tag, as for any variable.
fn trace_load_kind(kind: crate::kernel::LoadKind) -> String {
    if kind.is_word32() {
        "Bits32".into()
    } else {
        format!("{kind:?}")
    }
}

#[cfg(test)]
mod tests {
    use super::render_internal_proposition_labeled as render_proposition_labeled;
    use super::*;
    use crate::kernel::SharedIntegerTerm;

    #[test]
    fn old_projected_reads_keep_the_recorded_point_without_out_of_scope_values() {
        use crate::surface::{CodeRegionRef, ProgramPointKind, ProgramPointRef, RecordedStates};
        let _session = crate::kernel::VerificationSession::enter();
        let cell = Pointer::symbolic(Variable(989_100));
        let memory = Memory::new().with_block("unrelated", 4);
        let projected = crate::kernel::canonical_program_memory_for_pointer_load(&memory, &cell);
        let head = ExecutionState::new().with_memory(memory.clone());
        let mut retained_states = RecordedStates::new();
        retained_states.insert(
            ProgramPointRef {
                region: CodeRegionRef::Loop(0),
                kind: ProgramPointKind::Entry,
            },
            head,
        );
        let mut labels = MemoryStateLabels::default();
        // Fill the recent display with later, distinct memories. The exact
        // read-identity index must still name the old iteration entry.
        for index in 0..40 {
            // Metadata-only declarations retain the same read identity.
            // Real writes give these later points distinct program bytes.
            let state = ExecutionState::new().with_memory(
                Memory::new().with_block(format!("later{index}"), 4).store(
                    cell.clone(),
                    crate::kernel::ProgramValue::UInt64(MachineTerm::uint64_constant(index as u64)),
                ),
            );
            retained_states.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Exit,
                },
                state.clone(),
            );
            labels.source_state(&state, format!("region({index}).exit"));
        }
        labels.recorded_states(&retained_states);
        let description = labels.describe_state(&projected);
        assert!(description.contains("loop(0).entry"), "{description}");
        assert!(
            description.ends_with("projected for one read"),
            "{description}"
        );
        assert!(!description.contains("<pointer"), "{description}");
        assert!(!description.contains("<unnamed"), "{description}");
        labels.state_label(&projected);
        let legend = labels.trace_legend();
        assert!(legend.contains("loop(0).entry"), "{legend}");
        // Source annotations embedded in a trace have their own context;
        // they must not introduce a second numbered-label namespace.
        assert!(!legend.contains("value#"), "{legend}");
        assert!(!legend.contains("label definitions"), "{legend}");
    }

    fn render_proposition(proposition: &Proposition) -> String {
        render_proposition_labeled(proposition, &mut MemoryStateLabels::ambient())
    }

    #[test]
    fn shared_printer_distinguishes_successive_model_field_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let identity = Variable(988000);
        crate::kernel::model_fields::register_instance_spelling(identity, "c");
        for variable in [
            Variable(988001),
            Variable(988002),
            Variable(988003),
            Variable(988004),
        ] {
            crate::kernel::model_fields::register_model_field_variable(
                variable,
                crate::kernel::model_fields::ModelFieldOrigin {
                    identity,
                    field: "value".into(),
                    field_index: 0,
                    minted_by: crate::kernel::model_fields::ModelMint::CallReturn {
                        callee: "increment".into(),
                    },
                },
            );
        }
        let fact = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(988002))),
                right: Box::new(binary_node!(
                    Int32,
                    Add,
                    Box::new(MachineTerm::Variable(Variable(988001))),
                    Box::new(MachineTerm::constant(1)),
                )),
            },
            true,
        );
        let ordinary = super::render_proposition_labeled(&fact, &mut MemoryStateLabels::default());
        assert!(
            ordinary.contains("<unnamed A>") && ordinary.contains("<unnamed B>"),
            "{ordinary}"
        );
        let _typed = super::TypedNotationScope::enter();
        let mut labels = MemoryStateLabels::default();
        let rendered = super::render_proposition_labeled(&fact, &mut labels);
        assert!(rendered.contains("value A=c.value"), "{rendered}");
        assert!(rendered.contains("value B=c.value"), "{rendered}");
        assert_eq!(
            rendered,
            super::render_proposition_labeled(&fact, &mut labels)
        );
        assert!(!rendered.contains("c.value == (c.value + 1)"), "{rendered}");
        let integer = Proposition::Equal(
            Term::Integer(IntegerTerm::Variable(Variable(988003))),
            Term::Integer(IntegerTerm::Variable(Variable(988004))),
        );
        let rendered = super::render_proposition_labeled(&integer, &mut labels);
        assert!(rendered.contains("integer C=c.value"), "{rendered}");
        assert!(rendered.contains("integer D=c.value"), "{rendered}");
    }

    #[test]
    fn renders_integer_fold_and_scope() {
        let integer = IntegerTerm::Add(
            SharedIntegerTerm::from(IntegerTerm::from(2)),
            SharedIntegerTerm::from(IntegerTerm::from(3)),
        );
        let proposition = Proposition::ForAll {
            name: Default::default(),
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
    fn state_store_descriptions_keep_generated_rust_locals_private() {
        for (local, expected) in [
            ("__rust_mir_14", "the memory after a store"),
            ("total", "the memory after the store to `total`"),
        ] {
            let pointer = Pointer {
                block: format!("local:{local}").into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let memory = Memory::new().with_block(format!("local:{local}"), 4).store(
                pointer,
                crate::kernel::ProgramValue::Int32(MachineTerm::constant(7)),
            );
            assert_eq!(
                MemoryStateLabels::default().describe_state(&memory),
                expected
            );
        }
    }

    #[test]
    fn source_names_and_report_local_names_replace_variable_ids() {
        let mut labels = MemoryStateLabels::default();
        labels.source_name(Variable(7), "cur".into());
        let proposition = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(7))),
                right: Box::new(MachineTerm::Variable(Variable(8))),
            },
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
            crate::surface::diagnostics::describe_pure_fact(
                &proposition,
                ParameterBinding::default()
            ),
            "exists (path: Path<Integer>) { true }"
        );
    }

    #[test]
    fn click_fact_spelling_requires_named_non_load_operands() {
        let mut labels = MemoryStateLabels::default();
        labels.source_name(Variable(7), "r".into());
        let equality = |variable| {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(MachineTerm::Variable(variable)),
                    right: Box::new(MachineTerm::constant(0)),
                },
                false,
            )
        };
        assert_eq!(
            render_simple_click_fact_labeled(&equality(Variable(7)), &mut labels),
            Some("r != 0".into())
        );
        assert_eq!(
            render_simple_click_fact_labeled(&equality(Variable(8)), &mut labels),
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
        let fold = MachineTerm::RangeFold {
            start: Box::new(MachineTerm::constant(1)),
            end: Box::new(MachineTerm::constant(4)),
            initial: Box::new(MachineTerm::constant(0)),
            accumulator: crate::kernel::Variable(8),
            item: crate::kernel::Variable(9),
            body: Box::new(MachineTerm::Variable(crate::kernel::Variable(10))),
        };
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(fold),
            Term::Bitvector32(MachineTerm::constant(0)),
        ));
        assert!(rendered.contains("fold("));
        assert!(rendered.contains("acc=acc, item=item"), "{rendered}");
        assert!(rendered.contains("body=value A"), "{rendered}");
    }

    fn loadable_at(memory: Memory) -> Proposition {
        Proposition::MemoryLoadable {
            memory,
            base: Pointer {
                block: crate::kernel::PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: MachineTerm::constant(1),
            wide: false,
        }
    }

    /// A label says what a reader needs it to say: equal memory reads as one
    /// state whether or not it shares storage roots, and memory that differs
    /// reads as another. The five `Arc` addresses this used to print made two
    /// separately built empty states look like different memory.
    #[test]
    fn equal_states_share_one_label_and_different_memory_does_not() {
        let first = Memory::default();
        let shared = first.clone();
        let rebuilt = Memory::default();
        let different = Memory::new().with_block("block", 16);
        assert_ne!(first.diagnostic_identity(), rebuilt.diagnostic_identity());

        let first_text = render_proposition(&loadable_at(first));
        assert!(first_text.contains("state#1"), "{first_text}");
        assert_eq!(first_text, render_proposition(&loadable_at(shared)));
        assert_eq!(first_text, render_proposition(&loadable_at(rebuilt)));

        // Within one report the labels are the order of first appearance, so
        // two different memories are visibly two.
        let mut labels = MemoryStateLabels::default();
        let empty = render_proposition_labeled(&loadable_at(Memory::default()), &mut labels);
        let blocked = render_proposition_labeled(&loadable_at(different), &mut labels);
        assert!(empty.contains("state#1"), "{empty}");
        assert!(blocked.contains("state#2"), "{blocked}");
    }

    /// The comparison stops at its cap rather than growing with the report.
    #[test]
    fn state_labels_stop_comparing_past_their_cap() {
        let mut labels = MemoryStateLabels::default();
        for size in 0..MAX_MEMORY_STATE_LABELS as u32 {
            let memory = Memory::new().with_block(format!("block{size}"), 16);
            assert_eq!(labels.label(&memory), Some(size as usize + 1));
        }
        let overflowing = Memory::new().with_block("block0", 16);
        assert_eq!(
            labels.label(&overflowing),
            Some(1),
            "an earlier label still wins"
        );
        let beyond = Memory::new().with_block("beyond", 16);
        assert_eq!(labels.label(&beyond), None);
        let rendered = render_proposition_labeled(&loadable_at(beyond), &mut labels);
        assert!(rendered.contains("state<untracked>"), "{rendered}");
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
        let mut value = MachineTerm::constant(1);
        for _ in 0..128 {
            value = binary_node!(
                Int32,
                Add,
                Box::new(value),
                Box::new(MachineTerm::constant(1))
            );
        }
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(value),
            Term::Bitvector32(MachineTerm::constant(0)),
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
    fn machine_and_program_value_types_remain_visible() {
        let int32 = render_proposition(&Proposition::Equal(
            Term::ProgramValue(crate::kernel::ProgramValue::Int32(MachineTerm::constant(1))),
            Term::ProgramValue(crate::kernel::ProgramValue::UInt32(MachineTerm::constant(
                1,
            ))),
        ));
        assert!(int32.contains("int32(1)"));
        assert!(int32.contains("uint32(1)"));
    }

    #[test]
    fn trace_resource_names_its_arguments_without_debug_state() {
        let resource = ResourceFact::View(Resource::Token {
            name: "child_ref".into(),
            arguments: std::sync::Arc::from([AlgebraicValue::Program(
                crate::kernel::ProgramValue::Int32(MachineTerm::constant(7)),
            )]),
        });
        assert_eq!(render_resource_fact(&resource), "views child_ref(int32(7))");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    use crate::kernel::MemoryRange;
    // Even fallback rendering may receive native memory resources.
    #[test]
    fn wide_resource_diagnostics_keep_the_high_bits_of_bounds() {
        let wide = MemoryRange::new_wide(
            Pointer::symbolic(Variable(985_500)),
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1 << 33),
            4,
        );
        let fact = Proposition::ResourceContains {
            parent: Box::new(Resource::Memory(wide.clone())),
            child: Box::new(Resource::Memory(wide)),
        };
        let text = render_internal_proposition_labeled(&fact, &mut MemoryStateLabels::default());
        assert!(text.contains("8589934592"), "{text}");
    }
}

#[cfg(test)]
mod resource_detail_tests {
    use super::*;
    use crate::kernel::{
        IteratedGuard, IteratedMemory, ProgramType, ProgramValue, PublicationRight,
        PublicationSide, ResourceDescription, ResourceFieldSchema,
    };

    #[test]
    fn typed_resource_arguments_keep_publication_payload_values() {
        let flag = Pointer {
            block: "ready".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let publication = |value| {
            ResourceFact::own(Resource::Publication(PublicationRight::new(
                PublicationSide::Publisher,
                flag.clone(),
                ResourceDescription::new(
                    "payload".into(),
                    vec![AlgebraicValue::Program(ProgramValue::Int32(
                        MachineTerm::constant(value),
                    ))]
                    .into(),
                    ResourceFieldSchema::new(vec![]).unwrap(),
                ),
            )))
        };
        let first = render_resource_fact(&publication(7));
        let second = render_resource_fact(&publication(8));
        assert!(first.contains("payload(int32(7))"), "{first}");
        assert!(second.contains("payload(int32(8))"), "{second}");
        assert_ne!(first, second);
    }

    #[test]
    fn typed_iterated_resources_keep_guards_elements_and_taken_indices() {
        let base = Pointer {
            block: "elements".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let guard = Pointer {
            block: "flags".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let iterated = IteratedMemory::new(
            "selected",
            base,
            4,
            2,
            0,
            1,
            MachineTerm::constant(0),
            MachineTerm::constant(8),
            IteratedGuard::new(guard, ProgramType::Int32, 4, true, MachineTerm::constant(1)),
        )
        .unwrap();
        let render = |hole| {
            let fact = ResourceFact::own(Resource::Iterated(std::sync::Arc::new(
                iterated.with_hole(MachineTerm::constant(hole)),
            )));
            let mut labels = MemoryStateLabels::default();
            let mut text = render_resource_fact_labeled(&fact, &mut labels);
            text.push_str(&labels.trace_legend());
            text
        };
        let first = render(3);
        let second = render(5);
        assert!(
            first.contains("guard<Int32>(value#1[k], stride=4) == 1"),
            "{first}"
        );
        assert!(first.contains("element=memory("), "{first}");
        assert!(first.contains("holes=[3]"), "{first}");
        assert!(second.contains("holes=[5]"), "{second}");
        assert!(
            first.contains("flags") && first.contains("elements"),
            "{first}"
        );
        assert!(!first.contains("source binding unavailable"), "{first}");
    }
}
