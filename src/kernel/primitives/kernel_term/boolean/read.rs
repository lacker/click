//! Logical Boolean reads retain exact states and shared addresses. The
//! selected native descriptor is a lazy adapter for remaining native carriers.
use super::*;

pub type KernelBooleanRead = KernelMemoryRead;

impl KernelTerm {
    pub(crate) fn boolean_read(memory: SharedMemory, address: SharedPointerAddress) -> Self {
        Self::intern(
            KernelType::Bool,
            KernelTermNode::BoolRead(KernelMemoryRead::new(memory, address)),
        )
    }
    /// Explicit native read-leaf boundary, shared by diagnostics and stored-cell
    /// connection lookup. It never exports an enclosing Boolean expression.
    pub(crate) fn boolean_read_native(&self) -> Option<&ConditionTerm> {
        let KernelTermNode::BoolRead(read) = self.node() else {
            return None;
        };
        let (memory, address) = read.parts();
        let MachineTerm::BoolCast { value, .. } =
            self.0.machine_leaf.get_or_init(|| MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(ConditionTerm::BoolLoad(
                    memory.clone(),
                    Box::new(address.export().expect("retained Boolean read address")),
                )),
            })
        else {
            unreachable!("Boolean read descriptor");
        };
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn boolean_reads_keep_state_identity_and_exact_source() {
        let _session = crate::kernel::VerificationSession::enter();
        let before = Memory::new()
            .with_block("bool-read", 1)
            .with_block("bool-other", 4);
        let after = before.clone().store(
            Memory::global_pointer("bool-other"),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let sources = [before, after].map(|memory| {
            ConditionTerm::BoolLoad(
                intern_memory(memory),
                Box::new(Pointer {
                    block: PointerBlock::Symbolic(Variable(999301)),
                    offset: PointerOffsetTerm::Add(
                        Box::new(PointerOffsetTerm::Constant(0)),
                        Box::new(PointerOffsetTerm::scaled_int64_node(
                            MachineTerm::Variable(Variable(999302)),
                            8,
                            true,
                        )),
                    ),
                }),
            )
        });
        let roots = sources
            .each_ref()
            .map(|source| KernelTermImport::default().condition(source));
        for (root, source) in roots.iter().zip(&sources) {
            assert!(matches!(root.node(), KernelTermNode::BoolRead(_)));
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(root).unwrap()),
                format!("{source:?}")
            );
            assert_eq!(
                format!("{:?}", root.boolean_read_native().unwrap()),
                format!("{source:?}")
            );
            assert!(std::ptr::eq(
                root.boolean_read_native().unwrap(),
                root.boolean_read_native().unwrap()
            ));
            assert!(BooleanOperandView::Shared(root).is_bool_value_form());
            assert!(
                crate::kernel::memory_provenance::transport_framed_common_condition(
                    root,
                    &Memory::new(),
                    None
                )
                .is_none()
            );
        }
        assert!(
            !BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        assert!(
            !crate::kernel::assumptions::boolean_operands_equal_with_load_atoms(
                BooleanOperandView::Shared(&roots[0]),
                BooleanOperandView::Shared(&roots[1]),
                &|_, _| true
            )
        );
    }
    #[test]
    fn boolean_reads_preserve_native_substitution_states_and_addresses() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = intern_memory(Memory::new().with_block("bool-memory", 4).store(
            Memory::global_pointer("bool-memory"),
            ProgramValue::Int32(MachineTerm::Variable(Variable(999310))),
        ));
        let source = ConditionTerm::BoolLoad(
            memory,
            Box::new(Pointer {
                block: PointerBlock::Symbolic(Variable(999311)),
                offset: PointerOffsetTerm::scaled_int32_node(
                    MachineTerm::Variable(Variable(999310)),
                    4,
                ),
            }),
        );
        for source in [
            source.clone(),
            ConditionTerm::BoolEqual(Box::new(source), Box::new(ConditionTerm::Constant(false))),
        ] {
            let root = KernelTermImport::default().condition(&source);
            let bits = MachineTerm::constant(3);
            let expected = crate::kernel::reasoning::substitute_bitvector_variable_in_condition(
                &source,
                Variable(999310),
                &bits,
            );
            let actual =
                crate::kernel::reasoning::substitute_bitvector_variable_in_common_condition(
                    &root,
                    Variable(999310),
                    &bits,
                )
                .unwrap();
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                format!("{expected:?}")
            );
            let target = Pointer::null();
            let expected = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
                &Proposition::ConditionIs(source.clone(), true),
                Variable(999311),
                &target,
            );
            let Proposition::ConditionIs(expected, true) = expected else {
                panic!("condition");
            };
            let actual = crate::kernel::reasoning::substitute_pointer_variable_in_common_condition(
                &root,
                Variable(999311),
                &target,
            )
            .unwrap();
            assert_eq!(
                format!("{:?}", KernelTermExport::condition(&actual).unwrap()),
                format!("{expected:?}")
            );
        }
    }
    #[test]
    fn boolean_reads_separate_producer_arena_from_native_observation_identity() {
        let first = {
            let _session = crate::kernel::VerificationSession::enter();
            intern_memory(Memory::new())
        };
        let _session = crate::kernel::VerificationSession::enter();
        let second = intern_memory(Memory::new());
        assert_ne!(first.arena_id(), second.arena_id());
        assert_eq!(first, second);
        let roots = [first, second].map(|memory| {
            KernelTerm::boolean_read(
                memory,
                SharedPointerAddress::import(&Pointer::symbolic(Variable(999320))),
            )
        });
        assert_ne!(roots[0], roots[1]);
        assert!(
            BooleanOperandView::Shared(&roots[0])
                .syntax_equal(BooleanOperandView::Shared(&roots[1]))
        );
        let one = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(1));
        let zero = KernelTermImport::default()
            .machine(MachineIntegerType::Int32, &MachineTerm::constant(0));
        let observed = roots.map(|guard| {
            SharedMachineIntegerTerm::observe_shared(
                MachineIntegerType::Int32,
                KernelTerm::machine_if_shared(
                    MachineIntegerType::Int32,
                    [guard, one.clone(), zero.clone()],
                ),
            )
            .unwrap()
        });
        assert_eq!(observed[0], observed[1]);
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../../scaling_tests/kernel/primitives/kernel_term/boolean/read.rs");
}
