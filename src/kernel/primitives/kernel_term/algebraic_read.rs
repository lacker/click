//! Algebraic read syntax retains the producer's state and common address.
//! Memory selection and access evidence remain with the existing read producer.
use super::*;

impl KernelTerm {
    pub(crate) fn algebraic_read(
        ty: AlgebraicType,
        memory: SharedMemory,
        address: SharedPointerAddress,
    ) -> Self {
        Self::intern(
            KernelType::Algebraic(ty),
            KernelTermNode::AlgebraicRead(KernelMemoryRead::new(memory, address)),
        )
    }

    /// The native dependency reader treats an algebraic load as a Bits64
    /// carrier, including stored-load connections and havoc-range origins.
    pub(crate) fn algebraic_read_carrier(&self) -> Option<&MachineTerm> {
        let KernelTermNode::AlgebraicRead(read) = self.node() else {
            return None;
        };
        let (memory, address) = read.parts();
        Some(self.0.machine_leaf.get_or_init(|| {
            MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(address.export().expect("retained read address")),
                LoadKind::Bits64,
            )
        }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_reads_preserve_exact_states_types_and_observation_keys() {
        let first = {
            let _session = crate::kernel::VerificationSession::enter();
            intern_memory(Memory::new())
        };
        let _session = crate::kernel::VerificationSession::enter();
        let second = intern_memory(Memory::new());
        let ty = TypeParameterName::intern("RetainedReadT").algebraic_type();
        let pointer = Pointer {
            block: PointerBlock::Symbolic(Variable(999744)),
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(999745)),
                4,
            ),
        };
        let sources = [first, second].map(|memory| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::MemoryLoad {
                memory,
                pointer: Box::new(pointer.clone()),
            },
        });
        let roots = sources
            .each_ref()
            .map(|source| KernelTermImport::default().algebraic(source));
        assert_ne!(roots[0], roots[1], "producer arenas remain exact");
        assert!(roots[0].algebraic_syntax_equal(&roots[1]));
        let other_type = KernelTerm::algebraic_read(
            TypeParameterName::intern("OtherReadT").algebraic_type(),
            intern_memory(Memory::new()),
            SharedPointerAddress::import(&pointer),
        );
        assert!(!roots[0].algebraic_syntax_equal(&other_type));
        let changed_memory = KernelTerm::algebraic_read(
            ty.clone(),
            intern_memory(Memory::new().with_block("changed-read-retained_state", 8)),
            SharedPointerAddress::import(&pointer),
        );
        assert!(!roots[0].algebraic_syntax_equal(&changed_memory));
        let changed_address = KernelTerm::algebraic_read(
            ty.clone(),
            intern_memory(Memory::new()),
            SharedPointerAddress::import(&Pointer::symbolic(Variable(999750))),
        );
        assert!(!roots[0].algebraic_syntax_equal(&changed_address));
        let format = MachineIntegerType::Int32;
        let observed = roots.each_ref().map(|root| {
            let value = KernelTermExport::default().algebraic(root).unwrap();
            let KernelTermNode::AlgebraicRead(read) = root.node() else {
                panic!("common read")
            };
            let AlgebraicTermNode::MemoryLoad { memory, .. } = &value.node else {
                panic!("read output")
            };
            assert_eq!(memory.arena_id(), read.parts().0.arena_id());
            let variable = AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Variable(Variable(999746)),
            };
            let condition = KernelTerm::algebraic_equal_raw([
                root.clone(),
                KernelTermImport::default().algebraic(&variable),
            ]);
            let a = MachineTerm::constant(1);
            let b = MachineTerm::constant(2);
            let common = KernelTerm::machine_if_shared(
                format,
                [
                    condition,
                    KernelTermImport::default().machine(format, &a),
                    KernelTermImport::default().machine(format, &b),
                ],
            );
            let exports = KernelTermExport::machine_export_count();
            let key = SharedMachineIntegerTerm::observe_shared(format, common).unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let native = SharedMachineIntegerTerm::intern(
                format,
                MachineTerm::If {
                    condition: Box::new(ConditionTerm::AlgebraicEqual(
                        Box::new(value),
                        Box::new(variable),
                    )),
                    then_term: Box::new(a),
                    else_term: Box::new(b),
                },
            );
            assert_eq!(key, native);
            key
        });
        assert_eq!(observed[0], observed[1]);
        for (root, source) in roots.iter().zip(&sources) {
            assert_eq!(
                format!("{:?}", KernelTermExport::default().algebraic(root).unwrap()),
                format!("{source:?}")
            );
        }
    }
}
