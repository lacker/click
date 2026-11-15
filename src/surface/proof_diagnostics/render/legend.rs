//! Definitions for report-local labels, never additional proof evidence.
use super::*;
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{MemoryConstructionKind, MemoryDerivation, PointerBlock, ProgramValue};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, uint64_constant,
};

const MAX_ROUNDS: usize = 96;
const MAX_LEGEND_BYTES: usize = 12 * 1024;

fn short(text: &str) -> String {
    let mut end = text.len().min(300);
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    if end < text.len() {
        format!("{}…", &text[..end])
    } else {
        text.into()
    }
}

impl MemoryStateLabels {
    pub(crate) fn immutable_pointer_name(&mut self, pointer: &Pointer, name: &str) {
        if self.pointer_sources.len() < 128 {
            self.pointer_sources
                .entry(pointer.clone())
                .or_insert_with(|| short(name));
        }
    }

    // Anonymous identities remain distinct without presenting a mutable C local
    // as though it named this value at every program point.
    fn legend_symbol(&mut self, variable: Variable) -> String {
        let next = self.anonymous_names.len();
        self.anonymous_names
            .entry(variable)
            .or_insert_with(|| format!("symbol {}", alphabetic_label(next)))
            .clone()
    }

    fn legend_bits(&mut self, value: &MachineTerm) -> String {
        match value {
            bits32_constant!(value) => constant_u32(*value).to_string(),
            int64_constant!(value) => constant_i64(*value).to_string(),
            uint64_constant!(value) => constant_u64(*value).to_string(),
            MachineTerm::Variable(variable) => {
                if let Some((memory, address)) =
                    crate::kernel::registered_load_for_variable(variable)
                {
                    return format!(
                        "read({}, address {})",
                        self.memory_state_name(memory.memory()),
                        self.pointer_value_name(&address)
                    );
                }
                format!(
                    "<{}; source binding unavailable>",
                    self.legend_symbol(*variable)
                )
            }
            MachineTerm::MemoryLoad(memory, address, kind) => format!(
                "{}-byte read({}, address {})",
                kind.byte_width(),
                self.memory_state_name(memory.memory()),
                self.pointer_value_name(address)
            ),
            _ => {
                let mut renderer = Renderer {
                    output: String::new(),
                    nodes: 0,
                    depth: 0,
                    truncated: false,
                    labels: self,
                    bound_names: Vec::new(),
                    trace_facts: true,
                };
                renderer.bitvector(value);
                if renderer.truncated {
                    renderer.output.push('…');
                }
                renderer.output
            }
        }
    }

    fn legend_offset(&mut self, offset: &PointerOffsetTerm, depth: usize) -> String {
        if depth == 0 {
            return "<offset depth limit>".into();
        }
        match offset {
            PointerOffsetTerm::Constant(bytes) => format!("{bytes} bytes"),
            PointerOffsetTerm::Variable(variable) => {
                format!(
                    "({}) bytes",
                    self.legend_bits(&MachineTerm::Variable(*variable))
                )
            }
            PointerOffsetTerm::Add(left, right) => format!(
                "({} + {})",
                self.legend_offset(left, depth - 1),
                self.legend_offset(right, depth - 1)
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                format!(
                    "int32({}) * {byte_width} bytes",
                    self.legend_bits(value.structural_value())
                )
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                let kind = if *unsigned { "uint64" } else { "int64" };
                format!(
                    "{kind}({}) * {byte_width} bytes",
                    self.legend_bits(value.structural_value())
                )
            }
        }
    }

    pub(super) fn legend_pointer(&mut self, pointer: &Pointer) -> String {
        if pointer == &Pointer::null() {
            return "null pointer (0)".into();
        }
        if let Some(read) = pointer.as_loaded_value() {
            let retained_state = self.memory_state_name(read.defining_memory.memory());
            let address = self.pointer_value_name(&read.defining_address);
            let displacement = self.legend_offset(&read.displacement, 4);
            return format!(
                "pointer read at {retained_state}, address {address}, plus {displacement}"
            );
        }
        if let Some(MachineTerm::MemoryLoad(memory, address, _)) =
            crate::surface::proof_trace::pointer_definition(pointer)
        {
            return format!(
                "pointer read at {}, address {}",
                self.memory_state_name(memory.memory()),
                self.pointer_value_name(&address)
            );
        }
        // A source alias may name this immutable value, but its recorded
        // pure application explains which model and states produced it.
        if let PointerBlock::PureFunctionApplication(application) = &pointer.block {
            let mut renderer = Renderer {
                output: String::new(),
                nodes: 0,
                depth: 0,
                truncated: false,
                labels: self,
                bound_names: Vec::new(),
                trace_facts: true,
            };
            renderer.push(application.name());
            renderer.push("(");
            renderer.pure_arguments(application.arguments());
            renderer.push(")");
            if renderer.truncated {
                renderer.output.push('…');
            }
            let call = renderer.output;
            return format!("{call} + {}", self.legend_offset(&pointer.offset, 4));
        }
        // A temporary holding a callback is a source alias, not its definition.
        // Keep the function target or symbolic identity visible in the legend.
        match &pointer.block {
            PointerBlock::Concrete(name) if PointerBlock::is_global_name(name) => {
                return format!(
                    "object `{}` + {}",
                    short(name),
                    self.legend_offset(&pointer.offset, 4)
                );
            }
            PointerBlock::Function(name) => {
                return format!(
                    "function `{}` + {}",
                    short(name),
                    self.legend_offset(&pointer.offset, 4)
                );
            }
            PointerBlock::FunctionSymbolic(variable) => {
                let symbol = self.legend_symbol(*variable);
                return format!(
                    "symbolic function address {symbol} + {}",
                    self.legend_offset(&pointer.offset, 4)
                );
            }
            _ => {}
        }
        if let Some(name) = self.pointer_sources.get(pointer) {
            return name.clone();
        }
        // A field of a named pointer: `g + 16 bytes`, not the named pointer's
        // own construction spelled out with an anonymous symbol.
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            for (stem, shift) in [(left, right), (right, left)] {
                let PointerOffsetTerm::Constant(bytes) = shift.as_ref() else {
                    continue;
                };
                let stem = Pointer {
                    block: pointer.block.clone(),
                    offset: stem.as_ref().clone(),
                };
                if let Some(name) = self.pointer_sources.get(&stem) {
                    return format!("{name} + {bytes} bytes");
                }
            }
        }
        let base = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let base_name = if let Some(name) = self.pointer_sources.get(&base) {
            name.clone()
        } else {
            match &pointer.block {
                PointerBlock::Concrete(name) => format!("object `{}`", short(name)),
                PointerBlock::Symbolic(variable) | PointerBlock::ExternalObject(variable) => {
                    format!(
                        "<{}; source binding unavailable>",
                        self.legend_symbol(*variable)
                    )
                }
                PointerBlock::ExternalArgument => "external argument address base".into(),
                PointerBlock::Heap(_) => "<heap allocation; source origin unavailable>".into(),
                PointerBlock::Function(name) => format!("function `{}`", short(name)),
                _ => "<pointer base; source origin unavailable>".into(),
            }
        };
        format!("{base_name} + {}", self.legend_offset(&pointer.offset, 4))
    }

    fn legend_value(&mut self, value: &ProgramValue) -> String {
        match value {
            ProgramValue::Pointer(pointer) => self.pointer_value_name(pointer.pointer()),
            ProgramValue::Int32(bits)
            | ProgramValue::UInt32(bits)
            | ProgramValue::Int64(bits)
            | ProgramValue::UInt64(bits) => self.legend_bits(bits),
            _ => {
                let mut renderer = Renderer {
                    output: String::new(),
                    nodes: 0,
                    depth: 0,
                    truncated: false,
                    labels: self,
                    bound_names: Vec::new(),
                    trace_facts: true,
                };
                renderer.cvalue(value);
                if renderer.truncated {
                    renderer.output.push('…');
                }
                renderer.output
            }
        }
    }

    fn legend_ranges(&mut self, ranges: &[crate::kernel::MemoryRange]) -> String {
        let mut renderer = Renderer {
            output: String::new(),
            nodes: 0,
            depth: 0,
            truncated: false,
            labels: self,
            bound_names: Vec::new(),
            trace_facts: true,
        };
        renderer.push("[");
        for (index, range) in ranges.iter().enumerate() {
            if !renderer.visit() {
                break;
            }
            if index > 0 {
                renderer.push(", ");
            }
            renderer.resource(&crate::kernel::Resource::Memory(range.clone()));
        }
        renderer.push("]");
        if renderer.truncated {
            renderer.output.push('…');
        }
        renderer.output
    }

    fn legend_kept_frame(
        &mut self,
        ranges: &crate::kernel::ResourceContext,
        premises: &[(ConditionTerm, bool)],
    ) -> String {
        const LIMIT: usize = 128;
        let (count, facts) = ranges.diagnostic_facts(LIMIT);
        let mut retained = facts
            .map(|fact| render_resource_fact_labeled(fact, self))
            .collect::<Vec<_>>();
        if count > LIMIT {
            retained.push(format!(
                "… {} more ranges (call frame display limit)",
                count - LIMIT
            ));
        }
        let mut description = format!("caller frame retained [{}]", retained.join("; "));
        let mut placement = premises
            .iter()
            .take(LIMIT)
            .map(|(condition, value)| {
                render_proposition_labeled(
                    &Proposition::ConditionIs(condition.clone(), *value),
                    self,
                )
            })
            .collect::<Vec<_>>();
        if premises.len() > LIMIT {
            placement.push(format!(
                "… {} more premises (call frame display limit)",
                premises.len() - LIMIT
            ));
        }
        description.push_str(&format!("; placement premises [{}]", placement.join("; ")));
        description
    }

    fn legend_state(&mut self, memory: &Memory) -> String {
        let point = self
            .source_memories
            .iter()
            .find(|(known, point, _)| {
                point != "current" && (known.same_storage_roots(memory) || known == memory)
            })
            .map(|(_, point, _)| format!("recorded at {}; ", short(point)))
            .or_else(|| {
                self.recorded_memory_point(memory)
                    .map(|point| format!("program bytes recorded at {}; ", short(&point)))
            })
            .unwrap_or_default();
        // Labels denote memory contents, so a reconstruction equal to its
        // input gets the input's explanation. Otherwise structural label
        // reuse could produce "state#1 derived from state#1".
        // This bounded walk happens only while printing, never during checking.
        let mut described = memory;
        for _ in 0..MAX_ROUNDS {
            let Some(MemoryConstructionKind::Transform { sources, .. }) =
                described.diagnostic_construction()
            else {
                break;
            };
            let Some(source) = sources.iter().find(|source| *source == described) else {
                break;
            };
            described = source;
        }
        if let Some(MemoryConstructionKind::Transform { sources, .. }) =
            described.diagnostic_construction()
            && sources.iter().any(|source| source == described)
        {
            return format!("{point}equal-content construction chain omitted (legend limit)");
        }
        let memory = described;
        let edge = match memory.diagnostic_construction() {
            Some(MemoryConstructionKind::Transition(edge)) => edge.clone(),
            Some(MemoryConstructionKind::Transform {
                operation,
                sources,
                arguments,
            }) => {
                let bases = sources
                    .iter()
                    .map(|source| self.memory_state_name(source))
                    .collect::<Vec<_>>()
                    .join(", ");
                let args = arguments
                    .iter()
                    .map(|value| self.legend_value(value))
                    .collect::<Vec<_>>()
                    .join(", ");
                return format!("{point}{operation}({args}), based on {bases}");
            }
            None if memory.is_initial_diagnostic_memory() => {
                return format!("{point}initial empty memory");
            }
            None => {
                let shared = crate::kernel::intern_memory_ref(memory);
                let Some(edge) = shared.derivation() else {
                    return format!(
                        "{point}INTERNAL ERROR: state constructor did not record its origin"
                    );
                };
                edge
            }
        };
        let base = self.memory_state_name(edge.base().memory());
        let operation = match edge.as_ref() {
            MemoryDerivation::Store { pointer, value, .. } => {
                let address = self.pointer_value_name(pointer);
                let value = self.legend_value(value.native());
                format!("store {value} at address {address}")
            }
            MemoryDerivation::BranchJoin { incoming, .. } => {
                let inputs = incoming
                    .iter()
                    .map(|memory| self.memory_state_name(memory.memory()))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("join branch memories ({inputs})")
            }
            MemoryDerivation::CellObserved { .. } => "cache an observed cell".to_owned(),
            MemoryDerivation::CellsForgotten { .. } => {
                "cached cells forgotten (not a program write)".into()
            }
            MemoryDerivation::CallHavoc {
                mutable_ranges,
                kept_by_caller,
                ..
            } => {
                let ranges = self.legend_ranges(mutable_ranges);
                let mut description = format!("call effect: may write {ranges}");
                if let Some(kept) = kept_by_caller {
                    description.push_str("; ");
                    description.push_str(
                        &self.legend_kept_frame(
                            &kept.diagnostic_ranges(),
                            kept.diagnostic_premises(),
                        ),
                    );
                }
                description
            }
            MemoryDerivation::LoopHavoc { mutable_ranges, .. } => match mutable_ranges {
                Some(ranges) => format!("loop effect: may write {}", self.legend_ranges(ranges)),
                None => "loop effect: unknown write footprint".into(),
            },
            MemoryDerivation::BlockDeclared { block, .. } => {
                let address = self.pointer_value_name(&Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                });
                format!("declare block at {address}")
            }
            MemoryDerivation::LocalLifetimeEnded { block, .. } => {
                let address = self.pointer_value_name(&Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                });
                format!("end local lifetime at {address}")
            }
            MemoryDerivation::HeapAllocated { block, bytes, .. } => {
                let address = self.pointer_value_name(&Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(0),
                });
                let bytes = self.legend_bits(bytes);
                format!("allocate {bytes} bytes at {address}")
            }
            MemoryDerivation::HeapAllocationPending {
                allocation_base,
                bytes,
                ..
            }
            | MemoryDerivation::ContractAllocationRetired {
                allocation_base,
                bytes,
                ..
            }
            | MemoryDerivation::HeapFreed {
                allocation_base,
                bytes,
                ..
            } => {
                let address = self.pointer_value_name(allocation_base);
                let bytes = self.legend_bits(bytes);
                format!("{}({address}, {bytes} bytes)", edge.kind_name())
            }
            MemoryDerivation::ObjectInitializationRecorded { pointer, bytes, .. } => {
                let address = self.pointer_value_name(pointer);
                format!("record {bytes} initialized bytes at {address}")
            }
            MemoryDerivation::HeapAllocationFailed { .. } => "resolve failed allocation".into(),
            MemoryDerivation::ContractAllocationClaimsChanged { .. } => {
                "update contract allocation claims".into()
            }
            MemoryDerivation::CellsSeeded { run, .. } => {
                let address = self.pointer_value_name(run.base());
                let source = if run.source() == edge.base() {
                    "base".to_owned()
                } else {
                    self.memory_state_name(run.source())
                };
                let mode = match run.value_mode() {
                    crate::kernel::RunValueMode::Load => format!("reads from {source}"),
                    crate::kernel::RunValueMode::Copy { source_base } => format!(
                        "copy from {source} at {}",
                        self.pointer_value_name(source_base)
                    ),
                    crate::kernel::RunValueMode::Constant(value) => {
                        format!("constant {}", self.legend_value(value))
                    }
                };
                let holes = if run.holes().interval_count() == 0 {
                    String::new()
                } else {
                    format!(
                        ", holes {:?}{}",
                        run.holes()
                            .diagnostic_intervals()
                            .take(8)
                            .collect::<Vec<_>>(),
                        if run.holes().interval_count() > 8 {
                            "; further holes omitted (display limit)"
                        } else {
                            ""
                        }
                    )
                };
                format!(
                    "seed {} {:?} cells at {address}, stride {} bytes, {mode}{holes}",
                    run.count(),
                    run.element_type(),
                    run.element_width()
                )
            }
        };
        format!("{point}{operation}, based on {base}")
    }

    /// Expand references breadth-first under fixed entry/byte limits. Number
    /// order, rather than hash-map order, makes reports deterministic.
    pub(crate) fn trace_legend(&mut self) -> String {
        let states = self.state_legend();
        if self.pointer_values.is_empty() && self.memories.is_empty() {
            return states;
        }
        let mut output =
            String::from("\n\n  label definitions (recorded constructions, not additional facts):");
        if self.memories.len() > MAX_MEMORY_STATE_LABELS {
            output.push_str("\n    Beyond the first 32 retained_states, labels reuse retained identities only; separately constructed equal memories may have different labels.");
        }
        let (mut pointer_index, mut memory_index) = (1, 0);
        for _ in 0..MAX_ROUNDS {
            let mut added = false;
            if let Some(pointer) = self
                .pointer_values
                .iter()
                .find_map(|(pointer, index)| (*index == pointer_index).then(|| pointer.clone()))
            {
                let definition = self.legend_pointer(&pointer);
                output.push_str(&format!(
                    "\n    value#{pointer_index} = {}",
                    short(&definition)
                ));
                pointer_index += 1;
                added = true;
            }
            if let Some(memory) = self.memories.get(memory_index).cloned() {
                let definition = self.legend_state(&memory);
                output.push_str(&format!(
                    "\n    state#{} = {}",
                    memory_index + 1,
                    definition
                ));
                memory_index += 1;
                added = true;
            }
            if output.len() + 700 > MAX_LEGEND_BYTES || !added {
                break;
            }
        }
        if pointer_index <= self.pointer_values.len() || memory_index < self.memories.len() {
            output.push_str("\n    … additional label definitions omitted (legend limit)");
        }
        output.push_str(&states);
        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pure_pointer(name: &str, arguments: Vec<PureFunctionArgument>, bytes: i64) -> Pointer {
        Pointer {
            block: PointerBlock::PureFunctionApplication(
                crate::kernel::SharedPureApplication::intern(name.into(), arguments),
            ),
            offset: PointerOffsetTerm::Constant(bytes),
        }
    }

    #[test]
    fn pure_pointer_legend_distinguishes_typed_model_arguments_and_offsets() {
        let mut labels = MemoryStateLabels::default();
        for (id, name) in [(986_410, "left"), (986_411, "right")] {
            labels.source_name(Variable(id), name.into());
            let model = AlgebraicTerm {
                algebraic_type: crate::kernel::AlgebraicType::parameter("Model".into()),
                node: AlgebraicTermNode::Variable(Variable(id)),
            };
            let pointer =
                pure_pointer("identity", vec![PureFunctionArgument::Algebraic(model)], 16);
            labels.immutable_pointer_name(&pointer, "cached_child");
            labels.pointer_value_name(&pointer);
        }
        let text = labels.trace_legend();
        assert!(
            text.contains("value#1 = identity(left:Model) + 16 bytes"),
            "{text}"
        );
        assert!(
            text.contains("value#2 = identity(right:Model) + 16 bytes"),
            "{text}"
        );
        assert!(!text.contains("origin unavailable"), "{text}");
        assert_eq!(text, labels.trace_legend());
    }

    #[test]
    fn pure_pointer_legend_preserves_argument_states_and_nested_pointer_labels() {
        let base = Pointer {
            block: "local:p".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = Memory::new();
        let after = before
            .clone()
            .store(base.clone(), ProgramValue::Int32(7u32.into()));
        let mut labels = MemoryStateLabels::default();
        for memory in [before, after] {
            labels.pointer_value_name(&pure_pointer(
                "select",
                vec![PureFunctionArgument::ArrayRef {
                    memory,
                    pointer: ProgramValue::Pointer(crate::kernel::PointerValue::new(
                        base.clone(),
                        crate::kernel::ProgramType::Int32Pointer,
                    )),
                    element_type: crate::kernel::ProgramType::Int32,
                }],
                0,
            ));
        }
        let text = labels.trace_legend();
        assert!(
            text.contains("select(array-ref<int32>(state#1, ptr<int32*>(value#3)))"),
            "{text}"
        );
        assert!(
            text.contains("select(array-ref<int32>(state#2, ptr<int32*>(value#3)))"),
            "{text}"
        );
        assert!(
            text.contains("value#3 = object `local:p` + 0 bytes"),
            "{text}"
        );
        assert!(text.contains("store 7 at address value#3"), "{text}");
        assert_eq!(text, labels.trace_legend());
    }

    #[test]
    fn equal_content_reconstruction_has_a_definition_not_a_self_reference() {
        let pointer = Pointer {
            block: "local:unchanged".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = Memory::new()
            .with_uninitialized_object(pointer.clone(), 4)
            .with_uninitialized_object(pointer, 4);
        let mut labels = MemoryStateLabels::default();
        labels.memory_state_name(&memory);
        let text = labels.trace_legend();
        assert!(text.contains("based on state#2"), "{text}");
        assert!(!text.contains("based on state#1"), "{text}");
        assert!(text.contains("initial empty memory"), "{text}");
    }

    #[test]
    fn state_origin_survives_thread_and_arena_changes() {
        let memory = std::thread::spawn(|| {
            Memory::new().with_block("local:origin-test", 4).store(
                Pointer {
                    block: "local:origin-test".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramValue::Int32(MachineTerm::constant(9)),
            )
        })
        .join()
        .unwrap();
        let mut labels = MemoryStateLabels::default();
        labels.memory_state_name(&memory);
        let text = labels.trace_legend();
        assert!(text.contains("store 9 at address"), "{text}");
        assert!(text.contains("declare block at"), "{text}");
        assert!(text.contains("initial empty memory"), "{text}");
        assert!(!text.contains("INTERNAL ERROR"), "{text}");
    }

    #[test]
    fn proof_entry_construction_is_not_an_unknown_root() {
        let memory = Memory::new().with_uninitialized_block("local:object", 8);
        let mut labels = MemoryStateLabels::default();
        labels.memory_state_name(&memory);
        let text = labels.trace_legend();
        assert!(text.contains("mark uninitialized object"), "{text}");
        assert!(text.contains("declare uninitialized block"), "{text}");
        assert!(text.contains("initial empty memory"), "{text}");
        assert!(!text.contains("INTERNAL ERROR"), "{text}");
    }

    #[test]
    fn legend_defines_loaded_address_and_displacement_recursively() {
        let memory = crate::kernel::intern_memory(Memory::new());
        let base = Pointer::symbolic(Variable(986_401));
        let mut loaded = Pointer::loaded_value(&memory, &base);
        loaded.offset = PointerOffsetTerm::Constant(16);
        let mut labels = MemoryStateLabels::default();
        labels.immutable_pointer_name(&base, "zid");
        assert_eq!(labels.pointer_value_name(&loaded), "value#1");
        let text = labels.trace_legend();
        assert!(
            text.contains("value#1 = pointer read at state#1, address value#2, plus 16 bytes"),
            "{text}"
        );
        assert!(text.contains("value#2 = zid"), "{text}");
        assert!(text.contains("state#1 = initial empty memory"), "{text}");
        assert_eq!(text, labels.trace_legend());
    }

    #[test]
    fn legend_shows_recorded_store_and_its_base() {
        let address = Pointer::symbolic(Variable(986_402));
        let memory = Memory::new().store(
            address.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        );
        let mut labels = MemoryStateLabels::default();
        labels.immutable_pointer_name(&address, "p");
        labels.memory_state_name(&memory);
        let text = labels.trace_legend();
        assert!(
            text.contains("store 7 at address value#1, based on state#2"),
            "{text}"
        );
        assert!(text.contains("value#1 = p"), "{text}");
    }

    #[test]
    fn retained_frame_shows_ranges_and_placement_premises_without_shortening() {
        let pointer = Pointer::symbolic(Variable(986_405));
        let ranges =
            crate::kernel::ResourceContext::new().unchecked_with_facts((0..12).map(|index| {
                ResourceFact::own(Resource::Memory(
                    crate::kernel::MemoryRange::new_with_element_width(
                        pointer.clone(),
                        MachineTerm::constant(index),
                        MachineTerm::constant(index + 1),
                        8,
                    ),
                ))
            }));
        let condition = ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::constant(7)),
            right: Box::new(MachineTerm::constant(7)),
        };
        let premises = vec![(condition.clone(), true)];
        let mut labels = MemoryStateLabels::default();
        labels.immutable_pointer_name(&pointer, "node");
        let expected =
            render_proposition_labeled(&Proposition::ConditionIs(condition, true), &mut labels);
        let text = labels.legend_kept_frame(&ranges, &premises);
        assert!(text.len() > 300, "{text}");
        assert!(text.contains("Int32:11..12"), "{text}");
        assert!(
            text.contains(&format!("placement premises [{expected}]")),
            "{text}"
        );
        assert!(!text.contains("display limit"), "{text}");
        let many = vec![(ConditionTerm::Constant(true), true); 129];
        let text = labels.legend_kept_frame(&ranges, &many);
        assert!(
            text.contains("1 more premises (call frame display limit)"),
            "{text}"
        );
    }

    #[test]
    fn legend_names_only_matching_recorded_memories() {
        let memory = Memory::new().with_block("legend_recorded", 8);
        let mut labels = MemoryStateLabels::default();
        let naming = std::sync::Arc::new((Vec::new(), Vec::new()));
        labels
            .source_memories
            .push((Memory::new(), "unrelated_point".into(), naming.clone()));
        labels
            .source_memories
            .push((memory.clone(), "before_rotation".into(), naming));
        labels.memory_state_name(&memory);
        let text = labels.trace_legend();
        assert!(
            text.contains("state#1 = recorded at before_rotation;"),
            "{text}"
        );
        assert!(
            !text.contains("state#1 = recorded at unrelated_point;"),
            "{text}"
        );
    }

    #[test]
    fn legend_does_not_collapse_unknown_bases_or_use_mutable_names() {
        let mut labels = MemoryStateLabels::default();
        for id in [986_403, 986_404] {
            labels.source_name(Variable(id), "sibling".into());
            labels.pointer_value_name(&Pointer::symbolic(Variable(id)));
        }
        let text = labels.trace_legend();
        assert!(text.contains("symbol A"), "{text}");
        assert!(text.contains("symbol B"), "{text}");
        assert!(!text.contains("sibling"), "{text}");
    }

    #[test]
    fn legend_bounds_recursive_output_and_preserves_complete_trace() {
        let mut labels = MemoryStateLabels::default();
        for id in 0..128 {
            let pointer = Pointer::symbolic(Variable(987_000 + id));
            labels.immutable_pointer_name(&pointer, &"é".repeat(200));
            labels.pointer_value_name(&pointer);
        }
        let legend = labels.trace_legend();
        assert!(legend.len() <= MAX_LEGEND_BYTES);
        assert!(legend.contains("additional label definitions omitted"));
        let mut trace = "é".repeat(32 * 1024);
        trace.push_str("failure comparison retained");
        let original = trace.clone();
        crate::surface::proof_trace::append_legend(&mut trace, &mut labels);
        assert_eq!(trace, format!("{original}{legend}"));
    }
}
