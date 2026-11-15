//! Allocation-independent written syntax at the certification boundary.
//! No arithmetic observation, fact lookup, read resolution, or DAG export.
use super::*;
use crate::kernel::{KernelTermNode as N, PureFunctionArgument as A};
use std::collections::HashSet;

#[derive(Default)]
struct Comparison {
    seen: HashSet<(u64, u64)>,
}

pub(super) fn conditions_equal(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    Comparison::default().condition(left, right)
}

pub(super) fn algebraic_equal(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    Comparison::default().algebraic(left, right)
}

impl Comparison {
    fn algebraic(&mut self, left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
        use crate::kernel::AlgebraicTermNode as T;
        crate::instrumentation::record_deterministic_work(1);
        if left.algebraic_type != right.algebraic_type {
            return false;
        }
        match (&left.node, &right.node) {
            (T::Variable(a), T::Variable(b)) => a == b,
            (
                T::PureFunctionApplication {
                    name: an,
                    arguments: aa,
                },
                T::PureFunctionApplication {
                    name: bn,
                    arguments: ba,
                },
            ) => {
                an == bn
                    && aa.len() == ba.len()
                    && aa.iter().zip(ba).all(|(a, b)| self.argument(a, b))
            }
            (
                T::MemoryLoad {
                    memory: am,
                    pointer: ap,
                },
                T::MemoryLoad {
                    memory: bm,
                    pointer: bp,
                },
            ) => am.arena_id() == bm.arena_id() && self.pointer(ap, bp),
            // Match/conditional/constructor payloads keep their existing
            // certification route. This boundary admits only call syntax.
            _ => false,
        }
    }
    fn condition(&mut self, left: &ConditionTerm, right: &ConditionTerm) -> bool {
        use ConditionTerm as C;
        crate::instrumentation::record_deterministic_work(1);
        match (left, right) {
            (
                C::Compare {
                    format: a,
                    relation: ar,
                    left: al,
                    right: av,
                },
                C::Compare {
                    format: b,
                    relation: br,
                    left: bl,
                    right: bv,
                },
            ) => {
                a == b
                    && ar == br
                    && self.machine(Operand::Legacy(al), Operand::Legacy(bl))
                    && self.machine(Operand::Legacy(av), Operand::Legacy(bv))
            }
            (C::Constant(a), C::Constant(b)) => a == b,
            (C::Variable(a), C::Variable(b)) => a == b,
            // Other logical domains retain the existing certification route.
            _ => false,
        }
    }

    fn machine(&mut self, left: Operand<'_>, right: Operand<'_>) -> bool {
        let mut pending = vec![(left, right)];
        while let Some((left, right)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            if let (Operand::Shared(a), Operand::Shared(b)) = (left, right) {
                if a.ty() != b.ty() {
                    return false;
                }
                if a == b || !self.seen.insert((a.id(), b.id())) {
                    continue;
                }
                if let (N::MachineIf { arguments: a }, N::MachineIf { arguments: b }) =
                    (a.node(), b.node())
                {
                    // Retain exact guard identity; do not export a logical DAG.
                    if a[0] != b[0] {
                        return false;
                    }
                    pending.extend([
                        (Operand::Shared(&a[1]), Operand::Shared(&b[1])),
                        (Operand::Shared(&a[2]), Operand::Shared(&b[2])),
                    ]);
                    continue;
                }
            }
            if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
                (left.binary(), right.binary())
            {
                if af != bf || ao != bo {
                    return false;
                }
                pending.extend([(al, bl), (ar, br)]);
                continue;
            }
            if let (Some((ae, af, at, a)), Some((be, bf, bt, b))) = (left.cast(), right.cast()) {
                if (ae, af, at) != (be, bf, bt) {
                    return false;
                }
                pending.push((a, b));
                continue;
            }
            if let (Some((af, ao, a)), Some((bf, bo, b))) = (left.unary(), right.unary()) {
                if (af, ao) != (bf, bo) {
                    return false;
                }
                pending.push((a, b));
                continue;
            }
            if let (Some(a), Some(b)) = (left.literal(), right.literal()) {
                if a != b {
                    return false;
                }
                continue;
            }
            if let (Some(a), Some(b)) = (left.variable(), right.variable()) {
                if a != b {
                    return false;
                }
                continue;
            }
            if left.fold().is_some()
                || right.fold().is_some()
                || left.matched().is_some()
                || right.matched().is_some()
            {
                if !crate::kernel::machine_operand_syntax_cmp(left, right).is_eq() {
                    return false;
                }
                continue;
            }
            // Selected native leaves are already stored payloads, not exports.
            fn native(view: Operand<'_>) -> Option<&MachineTerm> {
                match view {
                    Operand::Legacy(term) => Some(term),
                    Operand::Shared(root) => root
                        .machine_conversion_leaf()
                        .or_else(|| root.machine_read_leaf()),
                }
            }
            let (Some(a), Some(b)) = (native(left), native(right)) else {
                return false;
            };
            match (a, b) {
                (
                    MachineTerm::ClickFunctionApplication {
                        name: an,
                        arguments: aa,
                    },
                    MachineTerm::ClickFunctionApplication {
                        name: bn,
                        arguments: ba,
                    },
                ) => {
                    if an != bn
                        || aa.len() != ba.len()
                        || !aa.iter().zip(ba).all(|(a, b)| self.argument(a, b))
                    {
                        return false;
                    }
                }
                (
                    MachineTerm::PureFunctionApplication {
                        name: an,
                        arguments: aa,
                    },
                    MachineTerm::PureFunctionApplication {
                        name: bn,
                        arguments: ba,
                    },
                ) => {
                    if an != bn || aa.len() != ba.len() {
                        return false;
                    }
                    pending.extend(
                        aa.iter()
                            .zip(ba)
                            .map(|(a, b)| (Operand::Legacy(a), Operand::Legacy(b))),
                    );
                }
                (
                    MachineTerm::If {
                        condition: ac,
                        then_term: at,
                        else_term: ae,
                    },
                    MachineTerm::If {
                        condition: bc,
                        then_term: bt,
                        else_term: be,
                    },
                ) => {
                    if !self.condition(ac, bc) {
                        return false;
                    }
                    pending.extend([
                        (Operand::Legacy(at), Operand::Legacy(bt)),
                        (Operand::Legacy(ae), Operand::Legacy(be)),
                    ]);
                }
                (MachineTerm::MemoryLoad(am, ap, ak), MachineTerm::MemoryLoad(bm, bp, bk)) => {
                    if am.arena_id() != bm.arena_id() || ak != bk || !self.pointer(ap, bp) {
                        return false;
                    }
                }
                // Unknown native domains are not granted a new equivalence.
                _ => return false,
            }
        }
        true
    }

    fn pointer(&mut self, a: &crate::kernel::Pointer, b: &crate::kernel::Pointer) -> bool {
        use crate::kernel::{PointerBlock as B, PointerOffsetTerm as O};
        let blocks = match (&a.block, &b.block) {
            (B::PureFunctionApplication(a), B::PureFunctionApplication(b)) => {
                a.name() == b.name()
                    && a.arguments().len() == b.arguments().len()
                    && a.arguments()
                        .iter()
                        .zip(b.arguments())
                        .all(|(a, b)| self.argument(a, b))
            }
            _ => a.block == b.block,
        };
        if !blocks {
            return false;
        }
        let mut pending = vec![(&a.offset, &b.offset)];
        while let Some((a, b)) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match (a, b) {
                (O::Constant(a), O::Constant(b)) if a == b => {}
                (O::Variable(a), O::Variable(b)) if a == b => {}
                (O::Add(al, ar), O::Add(bl, br)) => {
                    pending.extend([(al.as_ref(), bl.as_ref()), (ar.as_ref(), br.as_ref())])
                }
                (
                    O::Int32Scaled {
                        value: a,
                        byte_width: aw,
                    },
                    O::Int32Scaled {
                        value: b,
                        byte_width: bw,
                    },
                ) if aw == bw => {
                    if a.ty() != b.ty() || !self.machine(a.operand_view(), b.operand_view()) {
                        return false;
                    }
                }
                (
                    O::Int64Scaled {
                        value: a,
                        byte_width: aw,
                        unsigned: au,
                    },
                    O::Int64Scaled {
                        value: b,
                        byte_width: bw,
                        unsigned: bu,
                    },
                ) if aw == bw && au == bu => {
                    if a.ty() != b.ty() || !self.machine(a.operand_view(), b.operand_view()) {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    fn pointer_value(
        &mut self,
        a: &crate::kernel::PointerValue,
        b: &crate::kernel::PointerValue,
    ) -> bool {
        if !a.retained_nonaddress_metadata_eq(b) {
            return false;
        }
        if !self.pointer(a.pointer(), b.pointer())
            || !self.pointer(a.designation(), b.designation())
        {
            return false;
        }
        match (a.opaque_extent(), b.opaque_extent()) {
            (Some(a), Some(b)) if self.pointer(a, b) => {}
            (None, None) => {}
            _ => return false,
        }
        match (a.extent(), b.extent()) {
            (Some(a), Some(b)) => {
                self.pointer(&a.start, &b.start)
                    && self.machine(Operand::Legacy(&a.width), Operand::Legacy(&b.width))
            }
            (None, None) => true,
            _ => false,
        }
    }

    fn argument(&mut self, left: &A, right: &A) -> bool {
        fn scalar(value: &ProgramValue) -> Option<&MachineTerm> {
            match value {
                crate::kernel::integer_c_value!(term) => Some(term),
                ProgramValue::Bool(term)
                | ProgramValue::Float32(term)
                | ProgramValue::Float64(term) => Some(term),
                _ => None,
            }
        }
        match (left, right) {
            (A::SharedMachine(a), A::SharedMachine(b)) => {
                a.ty() == b.ty() && self.machine(a.operand_view(), b.operand_view())
            }
            (A::SharedMachine(a), A::Value(b)) | (A::Value(b), A::SharedMachine(a)) => {
                a.ty().program_type() == b.program_type()
                    && scalar(b).is_some_and(|b| self.machine(a.operand_view(), Operand::Legacy(b)))
            }
            (A::Value(a), A::Value(b)) => {
                if a.program_type() != b.program_type() {
                    return false;
                }
                match (scalar(a), scalar(b)) {
                    (Some(a), Some(b)) => self.machine(Operand::Legacy(a), Operand::Legacy(b)),
                    _ => match (a, b) {
                        (ProgramValue::Void, ProgramValue::Void) => true,
                        (ProgramValue::Pointer(a), ProgramValue::Pointer(b)) => {
                            self.pointer_value(a, b)
                        }
                        _ => false,
                    },
                }
            }
            (
                A::ArrayRef {
                    memory: am,
                    pointer: ap,
                    element_type: at,
                },
                A::ArrayRef {
                    memory: bm,
                    pointer: bp,
                    element_type: bt,
                },
            ) => {
                at == bt
                    && crate::kernel::intern_memory_ref(am).arena_id()
                        == crate::kernel::intern_memory_ref(bm).arena_id()
                    && self.argument(&A::Value(ap.clone()), &A::Value(bp.clone()))
            }
            (A::Algebraic(a), A::Algebraic(b)) => self.algebraic(a, b),
            // Unsupported Integer payloads retain the existing alpha route;
            // written syntax is never collapsed to numeric observation keys.
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, VerificationSession};

    fn retained_leaf(value: u32) -> KernelTerm {
        KernelTerm::retained_native_machine_operand(
            MachineIntegerType::UInt64,
            &MachineTerm::ClickFunctionApplication {
                name: "strict_leaf".into(),
                arguments: vec![A::Value(ProgramValue::Int32(MachineTerm::constant(value)))],
            },
        )
    }
    fn condition(argument: KernelTerm) -> ConditionTerm {
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt8,
            relation: CompareRelation::LessEqual,
            left: Box::new(MachineTerm::Constant {
                format: MachineIntegerType::UInt8,
                bits: 48,
            }),
            right: Box::new(MachineTerm::ClickFunctionApplication {
                name: "strict_digit".into(),
                arguments: vec![A::SharedMachine(
                    SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt64, argument)
                        .unwrap(),
                )],
            }),
        }
    }
    fn algebraic_call(argument: AlgebraicTerm, name: &str) -> AlgebraicTerm {
        let application = crate::kernel::SharedPureApplication::intern(
            "retained_length".into(),
            vec![A::Algebraic(argument.clone())],
        );
        let root = crate::kernel::KernelTermImport::default()
            .machine_call(MachineIntegerType::UInt64, &application);
        AlgebraicTerm {
            algebraic_type: argument.algebraic_type.clone(),
            node: crate::kernel::AlgebraicTermNode::PureFunctionApplication {
                name: name.into(),
                arguments: vec![
                    A::Algebraic(argument),
                    A::SharedMachine(
                        SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt64, root)
                            .unwrap(),
                    ),
                ],
            },
        }
    }

    #[test]
    fn algebraic_call_certification_ignores_allocation_but_keeps_written_inputs() {
        use crate::kernel::{AlgebraicTermNode, AlgebraicType, Memory, Pointer, Variable};
        let _session = VerificationSession::enter();
        let ty = AlgebraicType::parameter("T".into());
        let variable = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Variable(Variable(995950)),
        };
        let left = algebraic_call(variable.clone(), "wrap");
        let right = algebraic_call(variable.clone(), "wrap");
        assert_ne!(left, right);
        let claim = |value: AlgebraicTerm| {
            Proposition::Equal(Term::Algebraic(value), Term::Algebraic(variable.clone()))
        };
        let exports = KernelTermExport::machine_export_count();
        assert!(algebraic_equal(&left, &right));
        assert!(propositions_alpha_equivalent(
            &claim(left.clone()),
            &claim(right)
        ));
        assert!(!algebraic_equal(
            &left,
            &algebraic_call(variable.clone(), "other")
        ));
        let changed = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Variable(Variable(995951)),
        };
        assert!(!algebraic_equal(&left, &algebraic_call(changed, "wrap")));
        let memory = Memory::new();
        let other = memory
            .clone()
            .store(Pointer::null(), ProgramValue::Int32(1u32.into()));
        let read = |memory: &Memory| AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::MemoryLoad {
                memory: crate::kernel::intern_memory_ref(memory),
                pointer: Box::new(Pointer::null()),
            },
        };
        assert!(!algebraic_equal(
            &algebraic_call(read(&memory), "wrap"),
            &algebraic_call(read(&other), "wrap")
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    #[test]
    fn fresh_retained_payloads_have_one_written_certification_syntax() {
        let _session = VerificationSession::enter();
        let left = condition(retained_leaf(7));
        let right = condition(retained_leaf(7));
        assert_ne!(left, right, "exercise distinct producer IDs");
        let exports = KernelTermExport::machine_export_count();
        assert!(conditions_equal(&left, &right));
        let left = Proposition::ConditionIs(left, true);
        let right = Proposition::ConditionIs(right, true);
        assert!(propositions_alpha_equivalent(&left, &right));
        let lines = crate::kernel::fact_stability::capture(|| {
            crate::kernel::fact_stability::compare(
                "retained syntax",
                &left,
                &crate::kernel::fact_stability::FactFree::Term(right),
            );
        });
        assert!(lines.is_empty(), "{lines:?}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
    #[test]
    fn retained_syntax_rejects_changed_payload_operator_and_written_format() {
        let _session = VerificationSession::enter();
        assert!(!conditions_equal(
            &condition(retained_leaf(7)),
            &condition(retained_leaf(8))
        ));
        let binary = |operator| {
            KernelTerm::machine_binary_shared(
                MachineIntegerType::UInt64,
                operator,
                [retained_leaf(7), retained_leaf(9)],
            )
        };
        assert!(!conditions_equal(
            &condition(binary(MachineBinaryOp::Add)),
            &condition(binary(MachineBinaryOp::Subtract))
        ));
        let left = condition(retained_leaf(7));
        let mut right = left.clone();
        if let ConditionTerm::Compare { format, .. } = &mut right {
            *format = MachineIntegerType::Int8;
        }
        assert!(!conditions_equal(&left, &right));
        let mut right = left.clone();
        if let ConditionTerm::Compare { relation, .. } = &mut right {
            *relation = CompareRelation::LessThan;
        }
        assert!(!conditions_equal(&left, &right));
    }
    #[test]
    fn retained_syntax_keeps_states_and_pointer_qualifiers_exact() {
        let _session = VerificationSession::enter();
        let memory = crate::kernel::Memory::new();
        let changed = memory.clone().store(
            crate::kernel::Pointer::null(),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let read = |memory: &crate::kernel::Memory| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(memory),
                Box::new(crate::kernel::Pointer::null()),
                crate::kernel::LoadKind::Int32,
            )
        };
        assert!(!Comparison::default().machine(
            Operand::Legacy(&read(&memory)),
            Operand::Legacy(&read(&changed))
        ));
        let pointer = crate::kernel::PointerValue::new(
            crate::kernel::Pointer::null(),
            crate::kernel::ProgramType::Int32Pointer,
        );
        let qualified = pointer.clone().with_pointee_constant(true);
        assert!(!Comparison::default().argument(
            &A::Value(ProgramValue::Pointer(pointer)),
            &A::Value(ProgramValue::Pointer(qualified))
        ));
    }
    #[test]
    fn retained_syntax_preserves_argument_order_and_cast_spelling() {
        let _session = VerificationSession::enter();
        let call = |a, b| MachineTerm::ClickFunctionApplication {
            name: "ordered_call".into(),
            arguments: vec![a, b],
        };
        let argument = |value| {
            A::SharedMachine(
                SharedMachineIntegerTerm::from_shared(
                    MachineIntegerType::UInt64,
                    retained_leaf(value),
                )
                .unwrap(),
            )
        };
        let left = call(argument(7), argument(9));
        let right = call(argument(9), argument(7));
        assert!(!Comparison::default().machine(Operand::Legacy(&left), Operand::Legacy(&right)));
        let cast = |encoding, source, destination| {
            KernelTerm::machine_cast_shared(
                encoding,
                source,
                destination,
                KernelTerm::retained_native_machine_operand(
                    source,
                    &MachineTerm::Variable(crate::kernel::Variable(711)),
                ),
            )
        };
        let generic = cast(
            MachineCastSpelling::Generic,
            MachineIntegerType::UInt32,
            MachineIntegerType::UInt64,
        );
        let legacy = cast(
            MachineCastSpelling::UInt64From32,
            MachineIntegerType::UInt32,
            MachineIntegerType::UInt64,
        );
        let source = cast(
            MachineCastSpelling::Generic,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt64,
        );
        let destination = cast(
            MachineCastSpelling::Generic,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
        );
        for different in [&legacy, &source, &destination] {
            assert!(
                !Comparison::default()
                    .machine(Operand::Shared(&generic), Operand::Shared(different))
            );
        }
        assert!(
            Comparison::default().machine(Operand::Shared(&generic), Operand::Shared(&generic))
        );
    }

    #[test]
    fn retained_syntax_preserves_captured_and_pointer_index_states() {
        use crate::kernel::{
            LoadKind, Memory, Pointer, PointerOffsetTerm, PointerValue, ProgramType, Variable,
        };
        let _session = VerificationSession::enter();
        let memory = Memory::new();
        let other = memory.clone().store(
            Pointer::null(),
            ProgramValue::Int32(MachineTerm::constant(5)),
        );
        let pointer = |retained_state: &Memory| {
            PointerValue::new(
                Pointer {
                    block: "indexed".into(),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: SharedMachineIntegerTerm::index(
                            MachineIntegerType::Int32,
                            MachineTerm::MemoryLoad(
                                crate::kernel::intern_memory_ref(retained_state),
                                Box::new(Pointer::symbolic(Variable(712))),
                                LoadKind::Int32,
                            ),
                        ),
                        byte_width: 4,
                    },
                },
                ProgramType::Int32Pointer,
            )
        };
        let captured = |retained_state: &Memory, address| A::ArrayRef {
            memory: retained_state.clone(),
            pointer: ProgramValue::Pointer(address),
            element_type: ProgramType::Int32,
        };
        let left = captured(&memory, pointer(&memory));
        assert!(Comparison::default().argument(&left, &captured(&memory, pointer(&memory))));
        assert!(!Comparison::default().argument(&left, &captured(&other, pointer(&memory))));
        assert!(!Comparison::default().argument(&left, &captured(&memory, pointer(&other))));
    }

    #[test]
    fn retained_syntax_preserves_unchecked_evidence_and_hidden_declaration_class() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        use crate::kernel::{ObjectTypeEvidence, Pointer, PointerValue, ProgramType};
        let _session = VerificationSession::enter();
        let base = PointerValue::new(Pointer::null(), ProgramType::Int32Pointer);
        let class = CAccessClass::Scalar(CScalarClass::Int);
        let evidence = |fingerprint| ObjectTypeEvidence {
            class: class.clone(),
            checked: false,
            premise_fingerprint: fingerprint,
            premises: Default::default(),
        };
        let a = base.clone().with_object_type_evidence(Some(evidence(1)));
        let b = base.clone().with_object_type_evidence(Some(evidence(2)));
        assert_eq!(a.object_type_evidence(), b.object_type_evidence());
        assert_eq!(a.object_class(), b.object_class());
        assert!(!Comparison::default().pointer_value(&a, &b));
        let checked = ObjectTypeEvidence::from(class);
        let a = base
            .clone()
            .with_declared_object_class(Some(CAccessClass::Scalar(CScalarClass::Short)))
            .with_object_type_evidence(Some(checked.clone()));
        let b = base
            .with_declared_object_class(Some(CAccessClass::Scalar(CScalarClass::Long)))
            .with_object_type_evidence(Some(checked));
        assert_eq!(a.object_origin_evidence(), b.object_origin_evidence());
        assert_eq!(a.object_class(), b.object_class());
        assert!(!Comparison::default().pointer_value(&a, &b));
        assert!(Comparison::default().pointer_value(&a, &a.clone()));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../../scaling_tests/kernel/api/contract_certification/retained_syntax.rs");
    }
}
