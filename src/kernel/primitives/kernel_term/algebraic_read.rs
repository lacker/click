//! Algebraic read syntax retains the producer's state and common address.
//! SymbolicMemory selection and access evidence remain with the existing read producer.
use super::*;

impl KernelTerm {
    pub(crate) fn algebraic_read(
        ty: AlgebraicType,
        point: ProgramPoint,
        address: SharedAddress,
    ) -> Self {
        Self::intern(
            KernelType::Algebraic(ty),
            KernelTermNode::AlgebraicRead(KernelMemoryRead::new(point, address)),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn algebraic_reads_preserve_exact_states_types_and_observation_keys() {
        let first = {
            let _session = crate::kernel::VerificationSession::enter();
            intern_memory(SymbolicMemory::new())
        };
        let _session = crate::kernel::VerificationSession::enter();
        let second = intern_memory(SymbolicMemory::new());
        let ty = TypeParameterName::intern("RetainedReadT").algebraic_type();
        let pointer = Address::new(
            AddressBase::Symbolic(Variable(999744)),
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(999745)), 4),
        );
        let sources = [first, second].map(|memory| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::MemoryLoad {
                point: crate::kernel::ProgramPoint::at(&memory),
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
            crate::kernel::ProgramPoint::at(&intern_memory(SymbolicMemory::new())),
            pointer.shared().clone(),
        );
        assert!(!roots[0].algebraic_syntax_equal(&other_type));
        let changed_memory = KernelTerm::algebraic_read(
            ty.clone(),
            crate::kernel::ProgramPoint::at(&intern_memory(
                SymbolicMemory::new().with_block("changed-read-retained_state", 8),
            )),
            pointer.shared().clone(),
        );
        assert!(!roots[0].algebraic_syntax_equal(&changed_memory));
        let changed_address = KernelTerm::algebraic_read(
            ty.clone(),
            crate::kernel::ProgramPoint::at(&intern_memory(SymbolicMemory::new())),
            Address::symbolic(Variable(999750)).shared().clone(),
        );
        assert!(!roots[0].algebraic_syntax_equal(&changed_address));
        let format = MachineIntegerType::Int32;
        let observed = roots.each_ref().map(|root| {
            let value = KernelTermExport::default().algebraic(root).unwrap();
            let KernelTermNode::AlgebraicRead(read) = root.node() else {
                panic!("common read")
            };
            let AlgebraicTermNode::MemoryLoad { point: memory, .. } = &value.node else {
                panic!("read output")
            };
            assert_eq!(
                memory.shared_memory().arena_id(),
                read.parts().0.shared_memory().arena_id()
            );
            let variable = AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Variable(Variable(999746)),
            };
            let condition = KernelTerm::algebraic_equal_raw([
                root.clone(),
                KernelTermImport::default().algebraic(&variable),
            ]);
            let written = OldConditionTerm::AlgebraicEqual(Box::new(value), Box::new(variable));
            let stored = StoredConditionTerm::from(written.clone());
            assert_eq!(stored.root(), Some(&condition));
            let [left, _] = stored.operand_view().written_algebraic_equality().unwrap();
            let AlgebraicTermNode::MemoryLoad { point, .. } = &left.node else {
                panic!("stored read operand");
            };
            assert_eq!(
                point.shared_memory().arena_id(),
                read.parts().0.shared_memory().arena_id()
            );
            let a = OldMachineTerm::constant(1);
            let b = OldMachineTerm::constant(2);
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
                OldMachineTerm::If {
                    condition: Box::new(written),
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
