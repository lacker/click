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
    Address, AddressOffset, AlgebraicTerm, AlgebraicTermNode, AlgebraicValue, AlgebraicValueType,
    ExecutionState, ExpressionOutcome, IntegerRangeFoldIndex, IntegerTerm, OldConditionTerm,
    OldMachineTerm, ProgramValue, Proposition, PureFunctionArgument, Resource, Sort,
    SpecCaptureRefusal, SymbolicMemory, Term, Variable,
};
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{OffsetTree as _, OffsetView};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, uint64_constant,
};
use crate::surface::ParameterBinding;
use std::collections::{BTreeMap, HashMap};
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
/// twice means one memory and `state#1`/`state#2` means two, or one memory
/// that two reads name differently (the legend says which). Internal
/// variable IDs likewise become source names when the checked state provides
/// one, or distinct alphabetic labels when it does not.
#[derive(Clone, Default)]
pub(crate) struct MemoryStateLabels {
    memories: Vec<SymbolicMemory>,
    memory_identities: HashMap<(usize, usize, usize, usize, usize), usize>,
    trace_labels: bool,
    range_collisions: Option<range_collisions::RangeCollisions>,
    pointer_values: HashMap<Address, usize>,
    pointer_sources: HashMap<Address, String>,
    source_memories: Vec<(SymbolicMemory, String, std::sync::Arc<NamingTables>)>,
    current_point: Option<crate::kernel::program_point::ProgramPointId>,
    current_state: Option<ExecutionState>,
    source_points: HashMap<
        crate::kernel::program_point::ProgramPointId,
        (String, std::sync::Arc<NamingTables>),
    >,
    unnamed_points: HashMap<crate::kernel::program_point::ProgramPointId, usize>,
    /// Persistent source-point index, consulted only while printing. Older
    /// loop heads must not lose their name when the recent display fills up.
    recorded_states: Option<crate::surface::RecordedStates>,
    source_names: HashMap<Variable, String>,
    /// Exact structural reads held by source locals or recorded states.
    source_read_names: HashMap<OldMachineTerm, String>,
    source_types: HashMap<Variable, crate::kernel::ProgramType>,
    anonymous_names: HashMap<Variable, String>,
    /// How many placeholders (`<unnamed A>`, `<pointer A>`, `<state A>`)
    /// this report has printed, so a caller can tell whether a spelling was
    /// exact.
    placeholders: usize,
    /// Memories a source spelling names only by a report-local `<state A>`,
    /// defined after the report.
    unknown_states: Vec<SymbolicMemory>,
    /// Addresses a source spelling names only by a report-local
    /// `<pointer A>`.
    unnamed_pointers: HashMap<Address, String>,
    /// Addresses no structural spelling names, spelled as the pointer local
    /// that held them at a recorded state: `at(region(2).exit, p)`.
    recorded_pointers: HashMap<Address, String>,
    /// Slices no current name holds, by their count, spelled as the slice
    /// local or call result that held them at a recorded state:
    /// `at(statement(0).exit, view)`. Its data pointer is in
    /// `recorded_pointers` as `at(statement(0).exit, view.as_ptr())`.
    /// The flag is whether the slice is a string slice.
    recorded_slices: Vec<(OldMachineTerm, String, bool)>,
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
    /// Reads of one memory under different read names (a selected version
    /// point, or the memory itself) get labels of their own, so two reads
    /// that differ only in their read names do not print alike. Keyed by
    /// the memory's label and the read's version point.
    read_labels: HashMap<ReadLabelKey, usize>,
    /// For each label a read claimed: the memory's own label and the read's
    /// version point, which the legend states.
    read_label_versions: HashMap<usize, ReadLabelKey>,
    /// How many read names each memory's label is read under.
    read_names_per_memory: HashMap<usize, usize>,
}

/// A memory's label and the version point a read of it is named at.
type ReadLabelKey = (usize, Option<crate::kernel::program_point::ProgramPointId>);

/// The word a narrow value widened into 32 bits has (rule K8, a relation): a local
/// or parameter holding a promoted value is named, and typed, as the word
/// it holds, as it was when promotion reused the word. Only the widening is
/// read through; a σ keeps its own node.
fn widened_word(term: &OldMachineTerm) -> &OldMachineTerm {
    match term.narrow_widening32_operand() {
        Some((_, word)) => word,
        None => term,
    }
}

/// The binder a parameter's value is, if it is one: a scalar's variable, or
/// a `Bool` binder carried as its cast (Stage 5).
fn value_binder(term: &OldMachineTerm) -> Option<Variable> {
    match widened_word(term) {
        OldMachineTerm::Variable(variable) => Some(*variable),
        OldMachineTerm::BoolCast { value, .. } => match value.as_ref() {
            crate::kernel::OldConditionTerm::Variable(variable) => Some(*variable),
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
            && let OldMachineTerm::Variable(variable) = widened_word(term)
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
            crate::kernel::arithmetic_c_value!(OldMachineTerm::Variable(variable))
                if crate::kernel::registered_load_for_variable(variable).is_none()
                    && crate::kernel::model_fields::model_field_surface(*variable).is_none() =>
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
                self.fallback_pointer_name(pointer.address(), name.into());
            }
            _ => {}
        }
    }

    /// Stable report-local identities, distinct from source spellings.
    pub(crate) fn pointer_value_name(&mut self, pointer: &Address) -> String {
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
                let name =
                    crate::surface::surface_parameter_binding(parameter.binding_name()).to_string();
                // A Rust slice parameter is one slice: its data pointer is
                // `bytes.as_ptr()`, and the variable naming its count names
                // the slice (`design/rust-slice-values.md`, step 3b).
                if let Some(OldMachineTerm::Variable(counted)) = pointer.len()
                    && let Some(slice) = counted.counted_slice()
                {
                    labels.immutable_pointer_name(pointer.address(), &format!("{name}.as_ptr()"));
                    labels.immutable_pointer_name(&Address::symbolic(slice), &name);
                } else {
                    labels.immutable_pointer_name(pointer.address(), &name);
                }
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
            if matches!(widened_word(term), OldMachineTerm::MemoryLoad(..)) {
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
        let Some((memory, tables, id)) = AMBIENT_ENTRY.with(|entry| entry.borrow().clone()) else {
            return;
        };
        if self.source_memories.len() < MAX_MEMORY_STATE_LABELS
            && !self
                .source_memories
                .iter()
                .any(|(_, point, _)| point == ENTRY_POINT)
        {
            if let Some(id) = id {
                self.source_points
                    .insert(id, (ENTRY_POINT.into(), tables.clone()));
            }
            self.source_memories
                .push((memory, ENTRY_POINT.into(), tables));
        }
    }

    /// A memory as a phrase: `this state`, `function entry`, a recorded
    /// point, or a report-local `<state A>`.
    pub(crate) fn state_phrase(&mut self, memory: &SymbolicMemory) -> String {
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
    pub(crate) fn state_label(&mut self, memory: &SymbolicMemory) -> String {
        self.placeholders += 1;
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
    pub(crate) fn unnamed_pointer(&mut self, pointer: &Address) -> String {
        if let Some(name) = self.recorded_pointers.get(pointer) {
            return name.clone();
        }
        self.placeholders += 1;
        self.placeholder_pointer(pointer)
    }

    /// The name [`Self::unnamed_pointer`] falls back to before its
    /// placeholder, when one was registered.
    pub(crate) fn state_pointer_name(&self, pointer: &Address) -> Option<&str> {
        self.recorded_pointers.get(pointer).map(String::as_str)
    }

    /// A name for a pointer into `pointer`'s block at offset zero, when a
    /// local held one at the current state or at a recorded state: the
    /// base an address inside an allocation is spelled from. The current
    /// state's locals are preferred, then the shortest state name, so the
    /// choice does not depend on map order.
    pub(crate) fn block_base_name(&self, pointer: &Address) -> Option<&str> {
        fn shortest<'a>(names: &'a HashMap<Address, String>, pointer: &Address) -> Option<&'a str> {
            names
                .iter()
                .filter(|(base, _)| {
                    base.base == pointer.base
                        && matches!(base.offset.view(), OffsetView::Constant(0))
                })
                .map(|(_, name)| name.as_str())
                .min_by(|left, right| left.len().cmp(&right.len()).then(left.cmp(right)))
        }
        shortest(&self.pointer_sources, pointer)
            .or_else(|| shortest(&self.recorded_pointers, pointer))
    }

    /// A report-local `<pointer A>`, whatever else names the address.
    pub(crate) fn placeholder_pointer(&mut self, pointer: &Address) -> String {
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
        self.current_point = state.observation_point_id();
        self.current_state = Some(state.clone());
        // A parameter among the state's locals keeps its source declaration,
        // which the merge below would otherwise replace with a kernel type.
        let (names, values) = self.declared_local_naming_tables(state);
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

    fn recorded_memory_point(&self, memory: &SymbolicMemory) -> Option<String> {
        let memory = crate::kernel::intern_memory_ref(memory);
        let (selector, _) = self
            .recorded_states
            .as_ref()?
            .point_reading_memory(&memory)?;
        Some(crate::surface::diagnostics::describe_program_point_selector(selector))
    }

    /// `state`'s locals, each a parameter of the registered naming keeping
    /// that parameter's source declaration, so a struct-pointer parameter
    /// read at any point still spells its fields: `at(point, b->offset)`.
    fn declared_local_naming_tables(&self, state: &ExecutionState) -> NamingTables {
        let declarations = self
            .naming
            .as_deref()
            .map_or(&[][..], |(parameters, _)| parameters.as_slice());
        crate::surface::diagnostics::local_naming_tables_with_declarations(state, declarations)
    }

    pub(crate) fn source_state(&mut self, state: &ExecutionState, point: String) {
        if self.source_memories.len() < MAX_MEMORY_STATE_LABELS {
            let tables = self.declared_local_naming_tables(state);
            let tables = std::sync::Arc::new(tables);
            if let Some(id) = state.observation_point_id() {
                self.source_points
                    .insert(id, (point.clone(), tables.clone()));
            }
            self.source_memories
                .push((state.memory().clone(), point, tables));
        }
    }

    /// Resolve the observation's existing point identity. The memory
    /// naming table is for values and cannot distinguish equal-memory points.
    fn definedness_point_context(
        &mut self,
        id: crate::kernel::program_point::ProgramPointId,
    ) -> (Option<String>, Option<std::sync::Arc<NamingTables>>) {
        if self.current_point == Some(id) {
            return (None, self.naming.clone());
        }
        if let Some((name, tables)) = self.source_points.get(&id) {
            return (Some(name.clone()), Some(tables.clone()));
        }
        if let Some(points) = &self.recorded_states
            && let Some(selector) = points.point_name(id)
            && let Some(state) = points.get_exact(selector)
            && state.observation_point_id() == Some(id)
        {
            return (
                Some(crate::surface::diagnostics::describe_program_point_selector(selector)),
                Some(std::sync::Arc::new(
                    self.declared_local_naming_tables(state),
                )),
            );
        }
        let next = self.unnamed_points.len();
        let label = *self.unnamed_points.entry(id).or_insert(next);
        (
            Some(format!("<unrecorded point {}>", alphabetic_label(label))),
            None,
        )
    }

    fn source_memory_context(&self, memory: &SymbolicMemory) -> Option<(&str, &NamingTables)> {
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
    fn describe_state(&mut self, memory: &SymbolicMemory) -> String {
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
    pub(crate) fn fallback_pointer_name(&mut self, pointer: &Address, name: String) {
        if self.recorded_pointers.len() < 128 {
            self.recorded_pointers
                .entry(pointer.clone())
                .or_insert(name);
        }
    }

    /// Spells the slice whose count is `count` as `name`, when nothing named
    /// it that way yet.
    pub(crate) fn fallback_slice_name(&mut self, slice: &crate::kernel::Pointer, name: String) {
        let Some(count) = slice.len() else {
            return;
        };
        let string = slice.program_type()
            == crate::kernel::ProgramType::SlicePointer(crate::kernel::SliceElement::Str);
        if self.recorded_slices.len() < 128
            && !self
                .recorded_slices
                .iter()
                .any(|(known, _, _)| known == count)
        {
            self.recorded_slices.push((count.clone(), name, string));
        }
    }

    /// The name [`Self::fallback_slice_name`] gave the slice counted by
    /// `count`, and whether that slice is a string slice.
    pub(crate) fn recorded_slice_name(&self, count: &OldMachineTerm) -> Option<(&str, bool)> {
        self.recorded_slices
            .iter()
            .find(|(known, _, _)| known == count)
            .map(|(_, name, string)| (name.as_str(), *string))
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
    pub(crate) fn names_memory(&self, memory: &SymbolicMemory) -> bool {
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

    pub(crate) fn fallback_read_name(&mut self, read: &OldMachineTerm, name: String) {
        self.source_read_names.entry(read.clone()).or_insert(name);
    }

    fn source_read_name_for(&self, read: &OldMachineTerm) -> Option<&str> {
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

    /// A field name denotes the value currently held by that resource. The
    /// mint registry alone cannot name a field that was replaced or consumed.
    fn current_algebraic_field_name(
        &self,
        variable: Variable,
        term: &AlgebraicTerm,
    ) -> Option<String> {
        use crate::kernel::{ResourceFieldValue, model_fields};
        let origin = model_fields::registered_model_field_origin(variable)?;
        let instance = self
            .current_state
            .as_ref()?
            .resource_instance_fields(origin.identity)?;
        let held = match instance.fields().get(origin.field_index)? {
            ResourceFieldValue::Algebraic(value) => value,
            ResourceFieldValue::Program(crate::kernel::ProgramValue::Parameter(value)) => {
                value.as_ref()
            }
            _ => return None,
        };
        if held != term {
            return None;
        }
        let owner = origin.owner_spelling()?;
        Some(format!("{owner}.{}", origin.field))
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
    fn label(&mut self, memory: &SymbolicMemory) -> Option<usize> {
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

    /// The label of a read's memory: the memory's own label for the first
    /// read name it is read under, and a fresh label for each other one.
    fn read_label(&mut self, point: &crate::kernel::ProgramPoint) -> Option<usize> {
        let memory = self.label(point.memory())?;
        let key = (memory, point.read_version_id());
        if let Some(label) = self.read_labels.get(&key) {
            return Some(*label);
        }
        let claimed = self
            .read_names_per_memory
            .get(&memory)
            .copied()
            .unwrap_or(0);
        let label = if claimed == 0 {
            memory
        } else {
            let limit = if self.trace_labels {
                MAX_NODES
            } else {
                MAX_MEMORY_STATE_LABELS
            };
            if self.memories.len() >= limit {
                return Some(memory);
            }
            // The memory is the same; only the read name differs. Pushing it
            // again gives the read its own ordinal, while lookups by memory
            // still find the first one.
            self.memories.push(point.memory().clone());
            self.memories.len()
        };
        self.read_labels.insert(key, label);
        self.read_label_versions.insert(label, key);
        *self.read_names_per_memory.entry(memory).or_default() += 1;
        Some(label)
    }

    /// What tells a read-claimed label apart from the others over its
    /// memory, for the legend: the version point its reads are named at.
    /// Nothing for a memory read under one read name only.
    pub(super) fn read_label_note(&mut self, label: usize) -> Option<ReadLabelNote> {
        let (memory, version) = *self.read_label_versions.get(&label)?;
        if self
            .read_names_per_memory
            .get(&memory)
            .copied()
            .unwrap_or(0)
            < 2
        {
            return None;
        }
        let reads = match version {
            Some(id) => match self.definedness_point_context(id).0 {
                Some(point) => format!("reads named at version {point}"),
                None => "reads named at the current point's version".into(),
            },
            None => "reads named by the memory itself".into(),
        };
        Some(ReadLabelNote {
            same_memory_as: (label != memory).then_some(memory),
            reads,
        })
    }

    pub(crate) fn memory_state_name(&mut self, memory: &SymbolicMemory) -> String {
        self.label(memory).map_or_else(
            || "state<untracked>".to_owned(),
            |index| format!("state#{index}"),
        )
    }
}

/// How the legend tells apart labels over one memory that reads name
/// differently.
pub(super) struct ReadLabelNote {
    /// The memory's own label, for a label only a read name sets apart.
    pub(super) same_memory_as: Option<usize>,
    /// The read name: the version point, or the memory itself.
    pub(super) reads: String,
}

/// A comparison of full pointers can carry more information than their
/// common address contains.
fn distinct_pointers_at_one_address(
    left: &crate::kernel::Pointer,
    right: &crate::kernel::Pointer,
) -> bool {
    left != right && left.address() == right.address()
}

pub(super) fn pointer_comparison_needs_source(proposition: &Proposition) -> bool {
    matches!(proposition.old_condition(), Some((OldConditionTerm::PointerEqual(left, right), _))
        if distinct_pointers_at_one_address(left, right))
}

fn describe_pointer_comparison(address: &str, equality: bool) -> String {
    let relation = if equality { "equal" } else { "unequal" };
    format!("whether two pointers at `{address}` with different provenance are {relation}")
}

/// Whether the renderer spells `proposition` with no placeholder for an
/// unnamed value, pointer or state. Checked on a copy of `labels`, so asking
/// assigns no placeholder letters.
pub(crate) fn renders_exactly(proposition: &Proposition, labels: &MemoryStateLabels) -> bool {
    let mut trial = labels.clone();
    let before = trial.placeholders;
    let _ = render_proposition_labeled(proposition, &mut trial);
    trial.placeholders == before
}

impl MemoryStateLabels {
    pub(super) fn count_placeholder(&mut self) {
        self.placeholders += 1;
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
        &Proposition::condition_is(
            OldConditionTerm::Compare {
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
                Term::ProgramValue(value.clone().into()),
                Term::ProgramValue(
                    crate::kernel::ProgramValue::UInt64(resolution.expected.clone()).into(),
                ),
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
pub(crate) fn render_cell_address(pointer: &Address, labels: &mut MemoryStateLabels) -> String {
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
        "memory history without facts at the refusal stops at {retained_state}:\n    store: {} bytes at {written}\n    read range checked: {bytes} bytes at {read}{miss}\n    supplemental history explanation: equality and ownership facts at the refusal are not used by this walk, so a store the check itself crosses (by a quantified fact's guard, for one) can stop it; it does not say why the check failed",
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
pub(crate) struct CapturedNaming(Option<EntryNaming>);

type EntryNaming = (
    SymbolicMemory,
    std::sync::Arc<NamingTables>,
    Option<crate::kernel::program_point::ProgramPointId>,
);

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
            (Some((_, left, _)), Some((_, right, _))) => std::sync::Arc::ptr_eq(left, right),
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
        let Some((memory, tables, id)) = &self.0 else {
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
            if let Some(id) = id {
                labels
                    .source_points
                    .insert(*id, (ENTRY_POINT.into(), tables.clone()));
            }
            labels
                .source_memories
                .push((memory.clone(), ENTRY_POINT.into(), tables.clone()));
        }
    }
}

/// Whether `memory` is the initial memory, or it with cells seeded from it:
/// either holds exactly the values memory had before the code ran. A bounded
/// walk, done only while printing a failure.
fn is_entry_memory(memory: &SymbolicMemory) -> bool {
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
    static AMBIENT_ENTRY: std::cell::RefCell<Option<EntryNaming>> =
        const { std::cell::RefCell::new(None) };
    /// Set while a `--trace-proof` trace is rendered: traces keep their
    /// typed notation, which names each read's width and state.
    static TYPED_NOTATION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

thread_local! {
    // Source names retained by the linked interface, also used when raising
    // a library pointer back to a Surface term.
    static C_LIBRARY_POINTERS: std::cell::RefCell<BTreeMap<Variable, (String, crate::kernel::ProgramType)>> =
        const { std::cell::RefCell::new(BTreeMap::new()) };
}

pub(in crate::surface) struct CLibraryPointerNames(
    BTreeMap<Variable, (String, crate::kernel::ProgramType)>,
);

impl CLibraryPointerNames {
    pub(in crate::surface) fn enter(file: &crate::surface::ClickFile) -> Self {
        let pointers = file
            .c_library_values
            .iter()
            .filter_map(|(name, declaration)| {
                let ProgramValue::Pointer(pointer) = declaration.linked_value.as_ref()? else {
                    return None;
                };
                let crate::kernel::AddressBase::Symbolic(variable) = pointer.address().base else {
                    return None;
                };
                Some((variable, (name.clone(), pointer.program_type())))
            })
            .collect();
        Self(C_LIBRARY_POINTERS.replace(pointers))
    }
}

impl Drop for CLibraryPointerNames {
    fn drop(&mut self) {
        C_LIBRARY_POINTERS.replace(std::mem::take(&mut self.0));
    }
}

pub(in crate::surface) fn c_library_pointer_name(
    pointer: &crate::kernel::Address,
) -> Option<(String, crate::kernel::ProgramType)> {
    let crate::kernel::AddressBase::Symbolic(variable) = pointer.base else {
        return None;
    };
    if variable.producer() != Some(crate::kernel::Producer::CLibraryValue) {
        return None;
    }
    C_LIBRARY_POINTERS.with(|names| names.borrow().get(&variable).cloned())
}

/// Starts verifying a C function whose parameters hold `arguments` in the
/// memory `entry`.
pub(crate) fn enter_ambient_naming(
    parameter_binding: ParameterBinding<'_>,
    entry: &ExecutionState,
) {
    let tables = std::sync::Arc::new((
        parameter_binding.parameters.to_vec(),
        parameter_binding.arguments.to_vec(),
    ));
    AMBIENT_NAMING.with(|naming| *naming.borrow_mut() = Some(tables.clone()));
    AMBIENT_ENTRY.with(|slot| {
        *slot.borrow_mut() = Some((entry.memory().clone(), tables, entry.observation_point_id()))
    });
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

pub(super) fn typed_notation() -> bool {
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
        ResourceFact::Own(resource @ Resource::ConditionalMutexGuard(_), _) => {
            renderer.resource(resource)
        }
        ResourceFact::Own(resource, quantity) => {
            renderer.push("owns ");
            renderer.resource(resource);
            renderer.push(" x ");
            renderer.bitvector(quantity.old_form());
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

pub(in crate::surface) fn render_view_separation_goal(
    proposition: &Proposition,
    labels: &mut MemoryStateLabels,
) -> String {
    if !typed_notation()
        && let Proposition::ResourceSeparate { left, right } = proposition
    {
        return surface::source_separation(left, right, labels);
    }
    render_proposition_labeled(proposition, labels)
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
            Proposition::VolatileAccess(event) => {
                let operation = match event.kind {
                    crate::kernel::VolatileAccessKind::Read => "read",
                    crate::kernel::VolatileAccessKind::Write => "write",
                };
                self.fmt(format_args!("volatile-{operation}-event#{}(", event.id.0));
                self.pointer(&event.pointer);
                self.push(", ");
                self.cvalue(event.value.old_form());
                self.push(")");
            }
            Proposition::Equal(left, right) => self.binary_term(left, " = ", right),
            Proposition::SequenceMembership { element, .. } => {
                self.cvalue(element.old_form());
                self.push(" in sequence(<bounded opaque value>)");
            }
            Proposition::ConditionIs(condition, value) => {
                self.condition(condition.old_form());
                self.push(if *value { " is true" } else { " is false" });
            }
            Proposition::Predicate { name, arguments } => {
                if let Some(surface) =
                    crate::surface::proof::program_termination::predicate_spelling(name)
                {
                    self.push(&crate::surface::printing::source_click_proposition(
                        &surface,
                    ));
                    self.depth -= 1;
                    return;
                }
                // Type evidence about a pointer is written `is_a<T>(p)`.
                if let (Some(spelling), [pointer]) = (
                    crate::kernel::object_type_predicate_spelling(name),
                    arguments.as_slice(),
                ) {
                    self.push("is_a<");
                    self.push(spelling);
                    self.push(">(");
                    self.term(pointer);
                    self.push(")");
                    self.depth -= 1;
                    return;
                }
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
                self.push("predicate ");
                self.push(name);
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
                let name = self.variable_name(**var, "bound");
                self.fmt(format_args!("∀{name}:"));
                self.sort(sort);
                self.push(". ");
                self.bound_names.push((**var, name));
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
                    self.variable_name(**var, "bound")
                } else {
                    name.clone()
                };
                self.fmt(format_args!("∃{binder}:"));
                self.sort(sort);
                self.push(". ");
                self.bound_names.push((**var, binder));
                self.proposition(body);
                self.bound_names.pop();
            }
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide,
                ..
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
                self.bitvector(bytes.old_form());
                self.push(")");
            }
            Proposition::MemoryCanStore {
                memory,
                pointer,
                byte_width,
                ..
            } => {
                self.push("can-store(memory=");
                self.memory(memory);
                self.push(", pointer=");
                self.pointer(pointer);
                self.fmt(format_args!(", bytes={byte_width})"));
            }
            Proposition::MemoryReadDefined {
                at,
                memory,
                pointer,
                ..
            } => {
                self.push("defined-read(");
                if let Some(id) = at {
                    let (point, _) = self.labels.definedness_point_context(*id);
                    self.push(point.as_deref().unwrap_or("current"));
                    self.push(", ");
                }
                self.memory(memory);
                self.push(", ");
                self.pointer(pointer);
                self.push(")");
            }
            Proposition::MemoryLoads {
                memory,
                pointer,
                outcome,
                ..
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
            Proposition::ResourceViewable {
                memory, resource, ..
            } => {
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
                ..
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
                ..
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
                blocks,
                ..
            } => {
                self.push("heap-freed(");
                self.memory(before);
                self.push(" -> ");
                self.memory(after);
                for (base, bytes) in blocks {
                    self.push(", base=");
                    self.pointer(base);
                    self.push(", bytes=");
                    self.bitvector(bytes.bytes());
                }
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
            Proposition::ProgramStatementVerifies {
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
            Proposition::ProgramFunctionVerifies {
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
            Term::Condition(c) => self.condition(c.old_form()),
            Term::Bitvector32(v) => self.bitvector(v.old_form()),
            Term::Integer(i) => self.integer(i.old_form()),
            Term::PointerOffset(o) => self.offset(o.old_form(), 0),
            Term::ProgramValue(v) => self.cvalue(v.old_form()),
            Term::ArrayReadPoint(point) => self.memory(point.memory()),
            Term::ExecutionState(s) => self.state(s),
            Term::Sequence(_) => self.push("sequence(<bounded opaque value>)"),
            Term::Algebraic(value) => self.algebraic(value.old_form()),
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
                let name = if self.bound_names.iter().any(|(bound, _)| bound == variable)
                    || self.labels.source_name_for(*variable).is_some()
                {
                    self.variable_name(*variable, "value")
                } else {
                    self.labels
                        .current_algebraic_field_name(*variable, term)
                        .unwrap_or_else(|| self.variable_name(*variable, "value"))
                };
                self.fmt(format_args!("{name}:{}", term.algebraic_type.name))
            }
            AlgebraicTermNode::MemoryLoad {
                point: memory,
                pointer,
            } => self.bitvector(&AlgebraicTermNode::memory_load_carrier(
                memory,
                pointer,
                &term.algebraic_type,
            )),
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
                point: memory,
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
                self.memory(memory.memory());
                self.push(", ");
                self.cvalue(pointer);
                self.push(")");
            }
        }
        self.depth -= 1;
    }
    fn condition(&mut self, c: &OldConditionTerm) {
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
            OldConditionTerm::Constant(v) => self.push(if *v { "true" } else { "false" }),
            OldConditionTerm::Variable(v) => {
                let name = self.variable_name(*v, "condition");
                self.push(&name);
            }
            crate::kernel::integer_comparison_condition!(a, b) => {
                self.push("integer-condition(");
                self.integer_shared(a);
                self.push(match c {
                    OldConditionTerm::IntegerLessThan(..) => " < ",
                    OldConditionTerm::IntegerLessEqual(..) => " <= ",
                    OldConditionTerm::IntegerGreaterThan(..) => " > ",
                    OldConditionTerm::IntegerGreaterEqual(..) => " >= ",
                    OldConditionTerm::IntegerEqual(..) => " = ",
                    _ => " != ",
                });
                self.integer_shared(b);
                self.push(")");
            }
            OldConditionTerm::AlgebraicEqual(a, b) => {
                self.algebraic(a);
                self.push(" = ");
                self.algebraic(b);
            }
            OldConditionTerm::AddressOffsetEqual(a, b) => {
                self.offset(a, 0);
                self.push(" = ");
                self.offset(b, 0);
            }
            // A wide pointer is the slice of its address and element count,
            // as Rust spells an unrecorded construction.
            OldConditionTerm::PointerEqual(a, b) if a.is_wide() || b.is_wide() => {
                self.pointer_value(a);
                self.push(" == ");
                self.pointer_value(b);
            }
            OldConditionTerm::PointerEqual(a, b) => {
                if distinct_pointers_at_one_address(a, b) {
                    self.push("pointer equality at ");
                    self.pointer(a.address());
                    self.push(" (the two pointers have different provenance)");
                } else {
                    self.pointer(a.address());
                    self.push(" == ");
                    self.pointer(b.address());
                }
            }
            OldConditionTerm::AddressEqual(a, b) => {
                self.pointer(a);
                self.push(" = ");
                self.pointer(b);
            }
            OldConditionTerm::BoolApplication(application) => {
                self.push(application.name());
                self.push("(...)");
            }
            OldConditionTerm::BoolIf {
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
            OldConditionTerm::BoolEqual(a, b) => {
                self.push("bool(");
                self.condition(a);
                self.push(" = ");
                self.condition(b);
                self.push(")");
            }
            _ => self.push("condition(<bounded operation>)"),
        }
    }
    fn binary_condition_bv(&mut self, a: &OldMachineTerm, b: &OldMachineTerm, label: &str) {
        // Equality shares one 32-bit kernel form between signed and unsigned
        // C values. Retained type metadata disambiguates a returned value
        // even when it has no source name.
        let unsigned_equality = label == "int32 ="
            && [a, b].iter().any(|value| {
                matches!(value, OldMachineTerm::Variable(variable)
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
    fn comparison_bitvector(&mut self, value: &OldMachineTerm, signed: bool) {
        if signed && let bits32_constant!(value) = value {
            self.fmt(format_args!("{}", constant_u32(*value) as i32));
        } else {
            self.bitvector(value);
        }
    }
    fn overflow_condition_bv(
        &mut self,
        a: &OldMachineTerm,
        b: &OldMachineTerm,
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
                match crate::kernel::model_fields::model_field_surface(*variable) {
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
    /// A pointer value: its address, or for a wide pointer
    /// `slice::from_raw_parts(address, count)`.
    fn pointer_value(&mut self, value: &crate::kernel::Pointer) {
        match value.len() {
            Some(count) => {
                self.push("slice::from_raw_parts(");
                self.pointer(value.address());
                self.push(", ");
                self.bitvector(count);
                self.push(")");
            }
            None => self.pointer(value.address()),
        }
    }

    fn bitvector(&mut self, v: &OldMachineTerm) {
        if self.truncated || !self.visit() || self.depth >= MAX_DEPTH {
            self.truncated = true;
            return;
        }
        self.depth += 1;
        // Rule C1: a specification `Bool` travels as its cast to `uint8`,
        // which reads as the `Bool` itself.
        if let OldMachineTerm::BoolCast { to, value } = v {
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
        if let OldMachineTerm::MemoryLoad(retained_state, pointer, kind) = v {
            // `memory` prints its own memory label.
            if self.trace_facts {
                self.fmt(format_args!("read<{}>(", trace_load_kind(*kind)));
            } else {
                self.push("load(");
            }
            self.read_memory(retained_state);
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
        if let OldMachineTerm::Variable(variable) = v
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
            OldMachineTerm::Variable(v)
                if let Some(spelling) = crate::kernel::model_fields::model_field_surface(*v) =>
            {
                let name = self.variable_name(*v, "value");
                self.fmt(format_args!("{name}={spelling}"))
            }
            OldMachineTerm::Variable(v) => {
                let name = self.variable_name(*v, "value");
                self.push(&name);
            }
            binary_term!(Int32, Add, a, b) => self.binary_bv("+", a, b),
            binary_term!(Int32, Subtract, a, b) => self.binary_bv("-", a, b),
            binary_term!(Int32, Multiply, a, b) => self.binary_bv("*", a, b),
            _ if self.machine_operation(v) => {}
            OldMachineTerm::RangeFold {
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
            OldMachineTerm::PureFunctionApplication { name, arguments }
                if let Some(spelled) =
                    crate::kernel::layout_term_spelling(name, arguments.len()) =>
            {
                self.push(&crate::languages::display_source_names(&spelled));
            }
            OldMachineTerm::PureFunctionApplication { name, arguments } => {
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
            OldMachineTerm::ClickFunctionApplication { name, arguments } => {
                self.push(name);
                self.push("(");
                self.pure_arguments(arguments);
                self.push(")");
            }
            OldMachineTerm::AlgebraicMatch { scrutinee, arms } => {
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
            OldMachineTerm::IntegerAddress(pointer, _) => {
                self.push("address(");
                self.pointer(pointer);
                self.push(")");
            }
            OldMachineTerm::Cast {
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
    fn binary_bv(&mut self, op: &str, left: &OldMachineTerm, right: &OldMachineTerm) {
        self.push("(");
        self.bitvector(left);
        self.push(op);
        self.bitvector(right);
        self.push(")");
    }
    fn offset(&mut self, o: &AddressOffset, _depth: usize) {
        if self.depth >= MAX_DEPTH || self.truncated {
            self.truncated = true;
            return;
        }
        match o.view() {
            OffsetView::Constant(v) => self.fmt(format_args!("{v}")),
            OffsetView::Variable(v) => {
                let name = self.variable_name(v, "offset");
                self.push(&name);
            }
            OffsetView::Add(a, b) => {
                self.depth += 1;
                self.push("(");
                self.offset(a, 0);
                self.push("+");
                self.offset(b, 0);
                self.push(")");
                self.depth -= 1;
            }
            OffsetView::Int32Scaled { index, byte_width } => {
                self.push("int32(");
                self.bitvector(index.structural_value());
                self.fmt(format_args!(")*{byte_width} bytes"));
            }
            OffsetView::Int64Scaled {
                index,
                byte_width,
                unsigned,
            } => {
                self.push(if unsigned { "uint64(" } else { "int64(" });
                self.bitvector(index.structural_value());
                self.fmt(format_args!(")*{byte_width} bytes"));
            }
        }
    }
    fn pointer(&mut self, p: &Address) {
        if self.trace_facts {
            let name = if p == &Address::null() {
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
        if let Some(expression) = self
            .labels
            .recorded_states
            .as_ref()
            .and_then(|states| states.produced_address_expression(p))
        {
            self.push(&crate::surface::diagnostics::describe_contract_expression(
                &expression,
            ));
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
        match &p.base {
            crate::kernel::AddressBase::ReferenceCarrier { referent, instance } => self.fmt(
                format_args!("reference carrier of {referent} [{instance:?}]"),
            ),
            crate::kernel::AddressBase::AggregateReturn { frame } => {
                self.fmt(format_args!("result.storage(frame, {frame})"))
            }
            crate::kernel::AddressBase::ContractResult => self.push("result.storage()"),
            crate::kernel::AddressBase::ContractException => self.push("exception.storage()"),
            crate::kernel::AddressBase::StaticObject { binding } => {
                self.fmt(format_args!("{binding}.storage()"))
            }
            crate::kernel::AddressBase::AutomaticLocal { binding, instance } => {
                self.fmt(format_args!("{binding} [{instance:?}]"))
            }
            crate::kernel::AddressBase::PureFunctionApplication(application) => {
                self.push(application.name());
                self.push("(");
                self.pure_arguments(application.arguments());
                self.push(")");
            }
            crate::kernel::AddressBase::Concrete(s) | crate::kernel::AddressBase::Function(s) => {
                self.push(s)
            }
            crate::kernel::AddressBase::Heap(id) => self.fmt(format_args!("heap#{id}")),
            crate::kernel::AddressBase::Temporary(id) => self.fmt(format_args!("temporary#{id}")),
            crate::kernel::AddressBase::Symbolic(v)
            | crate::kernel::AddressBase::FunctionSymbolic(v)
            | crate::kernel::AddressBase::ExternalObject(v) => {
                let name = self.variable_name(*v, "pointer");
                self.push(&name);
            }
            crate::kernel::AddressBase::ExternalArgument => self.push("external"),
            crate::kernel::AddressBase::Load(load) => {
                self.fmt(format_args!("loaded-pointer#{}", load.id()))
            }
            crate::kernel::AddressBase::SliceData(load) => {
                self.fmt(format_args!("loaded-slice-data#{}", load.id()))
            }
            crate::kernel::AddressBase::StringLiteral { identity, .. } => {
                self.push(&identity.to_string())
            }
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
            Resource::ConditionalMutexGuard(carrier) => {
                self.push("if ");
                self.condition(carrier.condition());
                self.push(" { owns mutex_guard(");
                self.pointer(carrier.mutex());
                self.push("); }");
            }
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
                    self.resource_arguments(&(ty.arguments()).native_values());
                }
                self.push(")");
            }
            Resource::Publication(right) => {
                self.push(right.side().keyword());
                self.push("(");
                self.pointer(right.flag());
                self.push(", ");
                self.push(right.payload().family());
                self.resource_arguments(&(right.payload().arguments()).native_values());
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
                    self.algebraic_value(&argument.into_native());
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
                self.push(&crate::languages::display_source_names(name));
                self.resource_arguments(&(arguments).native_values());
            }
            Resource::Instance(instance) => {
                self.push("{");
                let identity = self.variable_name(instance.identity().variable(), "instance");
                self.push(&identity);
                self.push(": ");
                self.push(instance.name());
                self.resource_arguments(&(instance.arguments()).native_values());
                self.push(", fields=");
                self.resource_arguments(&instance.fields().native_values());
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
                    iterated.element_range(&OldMachineTerm::Variable(index)),
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
                    self.bitvector(hole.old_form());
                }
                self.push("])");
            }
        }
    }

    fn memory(&mut self, memory: &SymbolicMemory) {
        match self.labels.label(memory) {
            Some(label) => self.fmt(format_args!("state#{label}")),
            None => self.push("state<untracked>"),
        }
    }
    /// A read's memory, labeled by its read name as well as its contents.
    fn read_memory(&mut self, point: &crate::kernel::ProgramPoint) {
        match self.labels.read_label(point) {
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
    fn outcome(&mut self, outcome: &ExpressionOutcome<crate::kernel::StoredProgramValue>) {
        match outcome {
            ExpressionOutcome::Value(value) => self.cvalue(value.old_form()),
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
            crate::kernel::StatementOutcome::LoopTestFalse(_) => "loop-test-false",
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
/// signedness is the reader's tag, as for any variable. A read of a value of
/// algebraic type is named by its type, `read<T>`.
fn trace_load_kind(kind: crate::kernel::LoadKind) -> String {
    if kind.is_word32() {
        "Bits32".into()
    } else if let Some(algebraic_type) = kind.algebraic_type() {
        algebraic_type.name().into()
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
        let cell = Address::symbolic(Variable(989_100));
        let memory = SymbolicMemory::new().with_block("unrelated", 4);
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
                SymbolicMemory::new()
                    .with_block(format!("later{index}"), 4)
                    .store(
                        cell.clone(),
                        crate::kernel::ProgramValue::UInt64(OldMachineTerm::uint64_constant(
                            index as u64,
                        )),
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
    fn pointer_equality_diagnostic_keeps_provenance_distinct_at_the_same_address() {
        use crate::kernel::{Pointer, ProgramType, SubobjectBounds};
        let address = Address::symbolic(Variable(10993745));
        let left = Pointer::new(address.clone(), ProgramType::Int32Pointer);
        let right = left.clone().with_bounds(Some(SubobjectBounds::new(
            address,
            OldMachineTerm::uint64_constant(4),
        )));
        let goal = Proposition::condition_is(
            OldConditionTerm::PointerEqual(Box::new(left), Box::new(right)),
            true,
        );
        let mut labels = MemoryStateLabels::ambient();
        assert!(!renders_exactly(&goal, &labels));
        let ordinary = render_proposition_labeled(&goal, &mut labels);
        assert!(ordinary.contains("different provenance"), "{ordinary}");
        let trace = render_internal_proposition_labeled(&goal, &mut labels);
        assert!(trace.contains("different provenance"), "{trace}");
    }

    #[test]
    fn retained_contract_offset_diagnostic_preserves_shape_and_width() {
        use crate::kernel::{AddressOffset, OldMachineTerm, Term};
        let _session = crate::kernel::VerificationSession::enter();
        let offset = AddressOffset::raw_add(
            AddressOffset::scaled_int64_node(OldMachineTerm::uint64_constant(3), 8, true),
            AddressOffset::constant(-2),
        );
        let claim = Proposition::Equal(
            Term::PointerOffset(offset.into()),
            Term::PointerOffset(AddressOffset::constant(22).into()),
        );
        let source = surface::source(&claim, &mut MemoryStateLabels::ambient());
        assert!(source.contains(" * 8 + -2"), "{source}");
        let typed = render_internal_proposition_labeled(&claim, &mut MemoryStateLabels::ambient());
        assert!(typed.contains("uint64("), "{typed}");
        assert!(typed.contains("*8 bytes+-2)"), "{typed}");
    }

    #[test]
    fn shared_printer_distinguishes_successive_model_field_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let identity = crate::kernel::InstanceId::from_variable(Variable(988000));
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
        let fact = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(988002))),
                right: Box::new(binary_node!(
                    Int32,
                    Add,
                    Box::new(OldMachineTerm::Variable(Variable(988001))),
                    Box::new(OldMachineTerm::constant(1)),
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
            Term::Integer(IntegerTerm::Variable(Variable(988003)).into()),
            Term::Integer(IntegerTerm::Variable(Variable(988004)).into()),
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
        let proposition = crate::kernel::quantifiers::test_forall(
            Default::default(),
            crate::kernel::Variable(7),
            crate::kernel::Sort::Integer,
            Proposition::Equal(
                Term::Integer(integer.into()),
                Term::Integer(IntegerTerm::from(5).into()),
            ),
        );
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
            let pointer = Address::new(format!("local:{local}").into(), AddressOffset::constant(0));
            let memory = SymbolicMemory::new()
                .with_block(format!("local:{local}"), 4)
                .store(
                    pointer,
                    crate::kernel::ProgramValue::Int32(OldMachineTerm::constant(7)),
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
        let proposition = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(Variable(7))),
                right: Box::new(OldMachineTerm::Variable(Variable(8))),
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
        let proposition = crate::kernel::quantifiers::test_exists(
            "path".into(),
            Variable(7),
            Sort::Algebraic(path),
            Proposition::condition_is(OldConditionTerm::Constant(true), true),
        );
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
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(OldMachineTerm::Variable(variable)),
                    right: Box::new(OldMachineTerm::constant(0)),
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
        let mut proposition = Proposition::condition_is(OldConditionTerm::Constant(true), true);
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
            Proposition::condition_is(OldConditionTerm::IntegerLessThan(left, right), true);
        let rendered = render_proposition(&proposition);
        assert!(rendered.contains("integer-condition"));
        assert!(rendered.contains("<"));
        assert!(rendered.contains("11"));
        assert!(rendered.contains("19"));
    }

    #[test]
    fn range_fold_keeps_bounds_and_body_variables() {
        let fold = OldMachineTerm::RangeFold {
            start: Box::new(OldMachineTerm::constant(1)),
            end: Box::new(OldMachineTerm::constant(4)),
            initial: Box::new(OldMachineTerm::constant(0)),
            accumulator: crate::kernel::Variable(8),
            item: crate::kernel::Variable(9),
            body: Box::new(OldMachineTerm::Variable(crate::kernel::Variable(10))),
        };
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(fold.into()),
            Term::Bitvector32(OldMachineTerm::constant(0).into()),
        ));
        assert!(rendered.contains("fold("));
        assert!(rendered.contains("acc=acc, item=item"), "{rendered}");
        assert!(rendered.contains("body=value A"), "{rendered}");
    }

    fn loadable_at(memory: SymbolicMemory) -> Proposition {
        Proposition::MemoryLoadable {
            point: Default::default(),
            memory,
            base: Address::new(
                crate::kernel::AddressBase::ExternalArgument,
                AddressOffset::constant(0),
            ),
            bytes: (OldMachineTerm::constant(1)).into(),
            wide: false,
        }
    }

    /// A label says what a reader needs it to say: equal memory reads as one
    /// state whether or not it shares storage roots, and memory that differs
    /// reads as another. The five `Arc` addresses this used to print made two
    /// separately built empty states look like different memory.
    #[test]
    fn equal_states_share_one_label_and_different_memory_does_not() {
        let first = SymbolicMemory::default();
        let shared = first.clone();
        let rebuilt = SymbolicMemory::default();
        let different = SymbolicMemory::new().with_block("block", 16);
        assert_ne!(first.diagnostic_identity(), rebuilt.diagnostic_identity());

        let first_text = render_proposition(&loadable_at(first));
        assert!(first_text.contains("state#1"), "{first_text}");
        assert_eq!(first_text, render_proposition(&loadable_at(shared)));
        assert_eq!(first_text, render_proposition(&loadable_at(rebuilt)));

        // Within one report the labels are the order of first appearance, so
        // two different memories are visibly two.
        let mut labels = MemoryStateLabels::default();
        let empty =
            render_proposition_labeled(&loadable_at(SymbolicMemory::default()), &mut labels);
        let blocked = render_proposition_labeled(&loadable_at(different), &mut labels);
        assert!(empty.contains("state#1"), "{empty}");
        assert!(blocked.contains("state#2"), "{blocked}");
    }

    /// The comparison stops at its cap rather than growing with the report.
    #[test]
    fn state_labels_stop_comparing_past_their_cap() {
        let mut labels = MemoryStateLabels::default();
        for size in 0..MAX_MEMORY_STATE_LABELS as u32 {
            let memory = SymbolicMemory::new().with_block(format!("block{size}"), 16);
            assert_eq!(labels.label(&memory), Some(size as usize + 1));
        }
        let overflowing = SymbolicMemory::new().with_block("block0", 16);
        assert_eq!(
            labels.label(&overflowing),
            Some(1),
            "an earlier label still wins"
        );
        let beyond = SymbolicMemory::new().with_block("beyond", 16);
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
                Term::Integer(child.as_ref().clone().into()),
                Term::Integer(IntegerTerm::from(0).into()),
            ));
            assert!(rendered.len() <= MAX_BYTES + 64);
            if depth >= 32 {
                assert!(rendered.contains("truncated"));
            }
        }
    }

    #[test]
    fn deep_bitvector_tree_is_bounded() {
        let mut value = OldMachineTerm::constant(1);
        for _ in 0..128 {
            value = binary_node!(
                Int32,
                Add,
                Box::new(value),
                Box::new(OldMachineTerm::constant(1))
            );
        }
        let rendered = render_proposition(&Proposition::Equal(
            Term::Bitvector32(value.into()),
            Term::Bitvector32(OldMachineTerm::constant(0).into()),
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
            Term::Integer(fold.into()),
            Term::Integer(IntegerTerm::from(0).into()),
        ));
        assert!(rendered.contains("2"));
        assert!(rendered.contains("9"));
        assert!(rendered.contains("acc=acc, item=item"), "{rendered}");
        assert!(rendered.contains("body=(acc+item)"), "{rendered}");
    }

    #[test]
    fn machine_and_program_value_types_remain_visible() {
        let int32 = render_proposition(&Proposition::Equal(
            Term::ProgramValue(
                crate::kernel::ProgramValue::Int32(OldMachineTerm::constant(1)).into(),
            ),
            Term::ProgramValue(
                crate::kernel::ProgramValue::UInt32(OldMachineTerm::constant(1)).into(),
            ),
        ));
        assert!(int32.contains("int32(1)"));
        assert!(int32.contains("uint32(1)"));
    }

    #[test]
    fn trace_resource_names_its_arguments_without_debug_state() {
        let resource = ResourceFact::View(Resource::Token {
            name: "child_ref".into(),
            arguments: Vec::from([AlgebraicValue::Program(crate::kernel::ProgramValue::Int32(
                OldMachineTerm::constant(7),
            ))])
            .into(),
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
            Address::symbolic(Variable(985_500)),
            OldMachineTerm::uint64_constant(0),
            OldMachineTerm::uint64_constant(1 << 33),
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
        let flag = Address::new("ready".into(), AddressOffset::constant(0));
        let publication = |value| {
            ResourceFact::own(Resource::Publication(PublicationRight::new(
                PublicationSide::Publisher,
                flag.clone(),
                ResourceDescription::new(
                    "payload".into(),
                    vec![AlgebraicValue::Program(ProgramValue::Int32(
                        OldMachineTerm::constant(value),
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
        let base = Address::new("elements".into(), AddressOffset::constant(0));
        let guard = Address::new("flags".into(), AddressOffset::constant(0));
        let iterated = IteratedMemory::new(
            "selected",
            base,
            4,
            2,
            0,
            1,
            OldMachineTerm::constant(0),
            OldMachineTerm::constant(8),
            IteratedGuard::new(
                guard,
                ProgramType::Int32,
                4,
                true,
                OldMachineTerm::constant(1),
            ),
        )
        .unwrap();
        let render = |hole| {
            let fact = ResourceFact::own(Resource::Iterated(std::sync::Arc::new(
                iterated.with_hole(OldMachineTerm::constant(hole)),
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
