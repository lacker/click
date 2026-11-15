//! Typed diagnostic forms for facts without an exact source spelling.
use super::*;
#[cfg(test)]
use crate::kernel::binary_node;
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineBinaryOp, MachineIntegerType};
use crate::kernel::{MachineCastSpelling, MachineTerm};
use crate::kernel::{binary_term, unary_term};

impl Renderer<'_> {
    pub(super) fn resource_arguments(&mut self, arguments: &[AlgebraicValue]) {
        self.push("(");
        for (index, argument) in arguments.iter().enumerate() {
            if !self.visit() {
                break;
            }
            if index > 0 {
                self.push(", ");
            }
            self.algebraic_value(argument);
        }
        self.push(")");
    }

    pub(super) fn resource_composition(&mut self, context: &crate::kernel::ResourceContext) {
        const LIMIT: usize = 8;
        let (count, entries) = context.diagnostic_facts(LIMIT);
        self.push("validated-composition { ");
        for (index, fact) in entries.enumerate() {
            if !self.visit() {
                break;
            }
            if index > 0 {
                self.push("; ");
            }
            match fact {
                ResourceFact::Own(resource, quantity) => {
                    self.push("owns ");
                    self.resource(resource);
                    self.push(" x ");
                    self.bitvector(quantity);
                }
                ResourceFact::View(resource) => {
                    self.push("views ");
                    self.resource(resource);
                }
            }
        }
        if count > LIMIT {
            self.fmt(format_args!(
                "; … {} more entries (context display limit)",
                count - LIMIT
            ));
        }
        self.push("; support details omitted }");
    }

    /// Spell the operator as well as its numeric interpretation. A shared
    /// term arena does not make signed/unsigned or 32/64-bit operations equal.
    pub(super) fn machine_operation(&mut self, value: &MachineTerm) -> bool {
        use MachineTerm::*;
        let binary = match value {
            binary_term!(Int32, Divide, a, b) => Some((a, b, "bits32", "sdiv")),
            binary_term!(UInt32, Divide, a, b) => Some((a, b, "bits32", "udiv")),
            binary_term!(Int32, Remainder, a, b) => Some((a, b, "bits32", "srem")),
            binary_term!(UInt32, Remainder, a, b) => Some((a, b, "bits32", "urem")),
            binary_term!(Int32, ShiftLeft, a, b) => Some((a, b, "bits32", "<<")),
            binary_term!(Int32, ShiftRight, a, b) => Some((a, b, "bits32", "ashr")),
            binary_term!(UInt32, ShiftRight, a, b) => Some((a, b, "bits32", "lshr")),
            binary_term!(Int32, BitwiseAnd, a, b) => Some((a, b, "bits32", "&")),
            binary_term!(Int32, BitwiseOr, a, b) => Some((a, b, "bits32", "|")),
            binary_term!(Int32, BitwiseXor, a, b) => Some((a, b, "bits32", "^")),
            Binary {
                format,
                op,
                left: a,
                right: b,
            } => Some((a, b, format.name(), op.program_symbol())),
            _ => None,
        };
        if let Some((a, b, kind, operator)) = binary {
            self.push(kind);
            self.push("(");
            self.binary_bv(operator, a, b);
            self.push(")");
            return true;
        }
        let unary = match value {
            // A legacy-spelled conversion prints its spelling's name.
            Cast {
                spelling,
                value: inner,
                ..
            } if *spelling != MachineCastSpelling::Generic => Some((inner, spelling.name())),
            unary_term!(Int32, BitwiseNot, inner) => Some((inner, "BitwiseNot")),
            Unary {
                format,
                op: crate::kernel::MachineUnaryOp::BitwiseNot,
                operand: inner,
            } => Some((
                inner,
                match format {
                    crate::kernel::MachineIntegerType::UInt64 => "UInt64BitwiseNot",
                    _ => "Int64BitwiseNot",
                },
            )),
            _ => None,
        };
        if let Some((inner, name)) = unary {
            self.push(name);
            self.push("(");
            self.bitvector(inner);
            self.push(")");
            return true;
        }
        if let If {
            condition,
            then_term,
            else_term,
        } = value
        {
            self.push("if(");
            self.condition(condition);
            self.push(", ");
            self.bitvector(then_term);
            self.push(", ");
            self.bitvector(else_term);
            self.push(")");
            return true;
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{AlgebraicType, LoadKind, MemoryRange, ProgramValue, ResourceContext};

    fn render(fact: &Proposition) -> String {
        render_trace_fact_labeled(fact, &mut MemoryStateLabels::default())
    }

    #[test]
    fn inventory_fact_kinds_show_operands_instead_of_opaque_counts() {
        let p = Pointer::symbolic(Variable(986_700));
        let memory = Memory::new();
        let word = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory_ref(&memory),
            Box::new(p.clone()),
            LoadKind::Bits64,
        );
        let field = Resource::Memory(MemoryRange::new_with_element_width(
            p.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
            8,
        ));
        let composite = Resource::Composite {
            name: "rb_child_links".into(),
            arguments: std::sync::Arc::from([AlgebraicValue::Program(ProgramValue::Int32(
                MachineTerm::constant(7),
            ))]),
        };
        let model = AlgebraicTerm {
            algebraic_type: AlgebraicType::parameter("Tree".into()),
            node: AlgebraicTermNode::Variable(Variable(986_701)),
        };
        let context = ResourceContext::new().unchecked_with_fact(ResourceFact::Own(
            field.clone(),
            Box::new(MachineTerm::constant(1)),
        ));
        let facts = [
            (
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Binary {
                            format: MachineIntegerType::UInt64,
                            op: MachineBinaryOp::BitwiseAnd,
                            left: Box::new(word),
                            right: Box::new(MachineTerm::uint64_constant(1)),
                        }),
                        right: Box::new(MachineTerm::uint64_constant(0)),
                    },
                    true,
                ),
                "read<Bits64>",
            ),
            (
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::ClickFunctionApplication {
                            name: "rb_root_black".into(),
                            arguments: vec![PureFunctionArgument::Algebraic(model.clone())],
                        }),
                        right: Box::new(MachineTerm::constant(1)),
                    },
                    true,
                ),
                "rb_root_black(",
            ),
            (
                Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(Box::new(p.clone()), Box::new(Pointer::null())),
                    false,
                ),
                "is false",
            ),
            (
                Proposition::Equal(Term::Algebraic(model.clone()), Term::Algebraic(model)),
                ":Tree",
            ),
            (
                Proposition::ConditionIs(
                    ConditionTerm::PointerOffsetEqual(
                        Box::new(p.offset.clone()),
                        Box::new(PointerOffsetTerm::Constant(16)),
                    ),
                    true,
                ),
                "16",
            ),
            (
                Proposition::MemoryLoadable {
                    memory,
                    base: p,
                    bytes: MachineTerm::constant(8),
                    wide: false,
                },
                "bytes:uint32=8",
            ),
            (Proposition::ResourceComposition(context), "owns memory("),
            (
                Proposition::ResourceContains {
                    parent: Box::new(composite),
                    child: Box::new(field),
                },
                "rb_child_links(int32(7)) contains",
            ),
            (
                Proposition::Predicate {
                    name: "__click_volatile_write_123".into(),
                    arguments: vec![Term::ProgramValue(ProgramValue::UInt64(
                        MachineTerm::uint64_constant(1),
                    ))],
                },
                "volatile-write-event#123(uint64(1u64))",
            ),
        ];
        for (fact, expected) in facts {
            let text = render(&fact);
            assert!(text.contains(expected), "{text}");
            assert!(
                !text.contains("opaque")
                    && !text.contains("bounded operation")
                    && !text.contains("no exact"),
                "{text}"
            );
        }
    }

    #[test]
    fn trace_reads_preserve_state_and_load_kind_without_current_pointer_names() {
        let address = Pointer::symbolic(Variable(986_702));
        let first = crate::kernel::intern_memory(Memory::new());
        let second = crate::kernel::intern_memory(Memory::new().with_block("trace_changed", 4));
        let load = |memory, kind| {
            Term::Bitvector32(MachineTerm::MemoryLoad(
                memory,
                Box::new(address.clone()),
                kind,
            ))
        };
        let fact = Proposition::Equal(load(first, LoadKind::UInt8), load(second, LoadKind::Bits64));
        let mut labels = MemoryStateLabels::default();
        labels.source_name(Variable(986_702), "mutable_local".into());
        let text = render_trace_fact_labeled(&fact, &mut labels);
        assert!(
            text.contains("read<UInt8>(state#1, pointer=value#1)"),
            "{text}"
        );
        assert!(
            text.contains("read<Bits64>(state#2, pointer=value#1)"),
            "{text}"
        );
        assert!(!text.contains("mutable_local"));
    }

    #[test]
    fn resource_composition_lists_bounded_entries_and_explicit_omissions() {
        for count in [8, 64, 512] {
            let context = ResourceContext::new().unchecked_with_facts((0..count).map(|id| {
                ResourceFact::View(Resource::Token {
                    name: format!("token_{id}"),
                    arguments: std::sync::Arc::from([]),
                })
            }));
            let text = render(&Proposition::ResourceComposition(context));
            assert_eq!(text.matches("views token_").count(), 8, "{text}");
            assert_eq!(text.contains("more entries"), count > 8, "{text}");
            assert!(text.contains("support details omitted"));
            assert!(text.len() < 1024);
        }
    }

    #[test]
    fn machine_operations_keep_width_signedness_and_casts() {
        let a = Box::new(MachineTerm::Variable(Variable(986_703)));
        let b = Box::new(MachineTerm::constant(2));
        for (value, expected) in [
            (
                MachineTerm::Binary {
                    format: MachineIntegerType::Int64,
                    op: MachineBinaryOp::Divide,
                    left: a.clone(),
                    right: b.clone(),
                },
                "int64(",
            ),
            (
                MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Divide,
                    left: a.clone(),
                    right: b.clone(),
                },
                "uint64(",
            ),
            (
                binary_node!(UInt32, ShiftRight, a.clone(), b.clone()),
                "lshr",
            ),
            (binary_node!(Int32, ShiftRight, a.clone(), b), "ashr"),
            (
                MachineTerm::legacy_cast(MachineCastSpelling::UInt64FromInt32, a),
                "UInt64FromInt32(",
            ),
        ] {
            let text = render(&Proposition::Equal(
                Term::Bitvector32(value),
                Term::Bitvector32(MachineTerm::constant(0)),
            ));
            assert!(text.contains(expected), "{text}");
        }
    }
}

#[cfg(test)]
mod extended_state_tests {
    use super::*;

    #[test]
    fn trace_labels_retain_late_state_identities_without_more_structural_comparisons() {
        let mut labels = MemoryStateLabels::default();
        let fact = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
        render_trace_fact_labeled(&fact, &mut labels);
        let memories: Vec<_> = (0..64)
            .map(|i| Memory::new().with_block(format!("late_{i}"), 8))
            .collect();
        for (i, memory) in memories.iter().enumerate() {
            assert_eq!(labels.memory_state_name(memory), format!("state#{}", i + 1));
        }
        for (i, memory) in memories.iter().enumerate().rev() {
            assert_eq!(
                labels.memory_state_name(&memory.clone()),
                format!("state#{}", i + 1)
            );
        }
        assert!(
            labels
                .trace_legend()
                .contains("separately constructed equal memories")
        );
    }
}
