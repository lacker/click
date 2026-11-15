//! Pointer index reconstruction. Only selected native leaves enter the existing
//! memory authority checks; shared arithmetic is walked once per distinct node.
use super::*;
use crate::kernel::{
    KernelTerm, KernelTermNode, KernelType, MachineBinaryOp, MachineOperandView,
    SharedMachineIntegerTerm,
};
use std::collections::HashMap;

pub(super) fn transport_framed_index(
    value: &SharedMachineIntegerTerm,
    after: &Memory,
    assumptions: Option<(&PureFactContext, bool)>,
) -> Option<SharedMachineIntegerTerm> {
    map_index_with_guard(
        value,
        |leaf| transport_framed_atomic_bitvector(leaf, after, assumptions),
        crate::kernel::proof::equality_rewrite::rebuild_transported_machine_node,
        |_| true,
        |_| Ok(None),
        |guard| transport_framed_common_condition(guard, after, assumptions),
        &mut HashMap::new(),
    )
}

pub(super) fn normalize_exact_index(
    value: &SharedMachineIntegerTerm,
    assumptions: &PureFactContext,
) -> Option<SharedMachineIntegerTerm> {
    map_index(
        value,
        |leaf| Some(normalize_exact_memory_loads_in_bitvector(leaf, assumptions)),
        crate::kernel::proof::equality_rewrite::rebuild_normalized_machine_node,
    )
}

/// Native syntax equality without materializing a shared arithmetic tree.
pub(in crate::kernel) fn index_syntax_equal(
    left: &SharedMachineIntegerTerm,
    right: &SharedMachineIntegerTerm,
) -> bool {
    let left = KernelTerm::retained_machine_operand(left.ty(), left.operand_view());
    let right = KernelTerm::retained_machine_operand(right.ty(), right.operand_view());
    crate::kernel::shared_machine_syntax_equal(&left, &right)
}

pub(in crate::kernel) fn map_index(
    value: &SharedMachineIntegerTerm,
    map_leaf: impl Fn(&MachineTerm) -> Option<MachineTerm>,
    rebuild: impl Fn(&KernelTerm, &[KernelTerm]) -> Option<KernelTerm>,
) -> Option<SharedMachineIntegerTerm> {
    map_index_with_descent(value, map_leaf, rebuild, |root| {
        !matches!(root.node(), KernelTermNode::Fold(_))
    })
}

pub(in crate::kernel) fn map_index_with_descent(
    value: &SharedMachineIntegerTerm,
    map_leaf: impl Fn(&MachineTerm) -> Option<MachineTerm>,
    rebuild: impl Fn(&KernelTerm, &[KernelTerm]) -> Option<KernelTerm>,
    descend: impl Fn(&KernelTerm) -> bool,
) -> Option<SharedMachineIntegerTerm> {
    map_index_with_fold(value, map_leaf, rebuild, descend, |_| Ok(None))
}

pub(in crate::kernel) fn map_index_with_fold(
    value: &SharedMachineIntegerTerm,
    map_leaf: impl Fn(&MachineTerm) -> Option<MachineTerm>,
    rebuild: impl Fn(&KernelTerm, &[KernelTerm]) -> Option<KernelTerm>,
    descend: impl Fn(&KernelTerm) -> bool,
    map_fold: impl Fn(&KernelTerm) -> Result<Option<KernelTerm>, ()>,
) -> Option<SharedMachineIntegerTerm> {
    map_index_with_fold_and_cache(
        value,
        map_leaf,
        rebuild,
        descend,
        map_fold,
        &mut HashMap::new(),
    )
}

/// Reuse work across roots in one substitution scope. Callers own the memo;
/// neither states nor substitutions may change while it is reused.
pub(in crate::kernel) fn map_index_with_fold_and_cache(
    value: &SharedMachineIntegerTerm,
    map_leaf: impl Fn(&MachineTerm) -> Option<MachineTerm>,
    rebuild: impl Fn(&KernelTerm, &[KernelTerm]) -> Option<KernelTerm>,
    descend: impl Fn(&KernelTerm) -> bool,
    map_fold: impl Fn(&KernelTerm) -> Result<Option<KernelTerm>, ()>,
    results: &mut HashMap<u64, KernelTerm>,
) -> Option<SharedMachineIntegerTerm> {
    map_index_with_guard(
        value,
        &map_leaf,
        rebuild,
        descend,
        map_fold,
        |condition| {
            let guard = MachineTerm::BoolCast {
                to: MachineIntegerType::UInt8,
                value: Box::new(crate::kernel::KernelTermExport::condition(condition).ok()?),
            };
            let mapped = map_leaf(&guard)?;
            Some(if mapped == guard {
                condition.clone()
            } else {
                crate::kernel::KernelTermImport::default()
                    .condition(&ConditionTerm::truth_of_bool_word(&mapped))
            })
        },
        results,
    )
}

fn map_index_with_guard(
    value: &SharedMachineIntegerTerm,
    map_leaf: impl Fn(&MachineTerm) -> Option<MachineTerm>,
    rebuild: impl Fn(&KernelTerm, &[KernelTerm]) -> Option<KernelTerm>,
    descend: impl Fn(&KernelTerm) -> bool,
    map_fold: impl Fn(&KernelTerm) -> Result<Option<KernelTerm>, ()>,
    map_guard: impl Fn(&KernelTerm) -> Option<KernelTerm>,
    results: &mut HashMap<u64, KernelTerm>,
) -> Option<SharedMachineIntegerTerm> {
    let Some(root) = value.shared_operand() else {
        return Some(SharedMachineIntegerTerm::index(
            value.ty(),
            map_leaf(value.retained_written_operand()?)?,
        ));
    };
    // Authority is local to this invocation: no answer survives a changed
    // state, fact context, registry, or direct-versus-general frame policy.
    let mut pending = vec![(root, false)];
    while let Some((node, finish)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if results.contains_key(&node.id()) {
            continue;
        }
        if matches!(
            node.node(),
            KernelTermNode::Fold(_) | KernelTermNode::Match(_)
        ) && let Some(mapped) = map_fold(node).ok()?
        {
            results.insert(node.id(), mapped);
            continue;
        }
        // Native matches are opaque to memory transport; explicit scoped
        // substitutions above may still rewrite them.
        if matches!(node.node(), KernelTermNode::Match(_)) {
            results.insert(node.id(), node.clone());
            continue;
        }
        let children: Vec<_> = match node.node() {
            KernelTermNode::Fold(fold) => fold.arguments.iter().collect(),
            KernelTermNode::MachineIf { arguments } => arguments[1..].iter().collect(),
            KernelTermNode::MachineBinary { arguments, .. } => arguments.iter().collect(),
            KernelTermNode::MachineUnary { operand, .. }
            | KernelTermNode::MachineCast { operand, .. } => vec![operand],
            _ => vec![],
        };
        if !children.is_empty() && !descend(node) {
            results.insert(node.id(), node.clone());
            continue;
        }
        if !finish && !children.is_empty() {
            pending.push((node, true));
            pending.extend(children.into_iter().rev().map(|child| (child, false)));
            continue;
        }
        let rewritten = if children.is_empty() {
            let view = MachineOperandView::Shared(node);
            let leaf = view
                .literal()
                .map(std::borrow::Cow::Owned)
                .or_else(|| view.read_source())?;
            let next = map_leaf(&leaf)?;
            let KernelType::Program(ty) = node.ty() else {
                return None;
            };
            node.rewritten_machine_leaf(MachineIntegerType::from_program_type(*ty)?, &leaf, &next)
        } else {
            let children: Vec<_> = children
                .iter()
                .map(|child| results[&child.id()].clone())
                .collect();
            if let KernelTermNode::MachineIf { arguments } = node.node() {
                let condition = map_guard(&arguments[0])?;
                let KernelType::Program(ty) = node.ty() else {
                    return None;
                };
                let updated = KernelTerm::machine_if_shared(
                    MachineIntegerType::from_program_type(*ty)?,
                    [condition, arguments[1].clone(), arguments[2].clone()],
                );
                rebuild(&updated, &children)?
            } else {
                rebuild(node, &children)?
            }
        };
        results.insert(node.id(), rewritten);
    }
    SharedMachineIntegerTerm::from_shared(value.ty(), results.get(&root.id())?.clone())
}
// Preserve scale_int32/scale_int64's literal and signed-extension rules.
// The destination already accepts a retained operand; it is not a native
// output boundary.
pub(in crate::kernel) fn transported_scaled_index(
    value: SharedMachineIntegerTerm,
    byte_width: i64,
    wide: Option<bool>,
) -> PointerOffsetTerm {
    let view = value.operand_view();
    if let Some(native) = view
        .literal()
        .map(std::borrow::Cow::Owned)
        .or_else(|| match view {
            MachineOperandView::Shared(root)
                if matches!(root.node(), KernelTermNode::Call { .. }) =>
            {
                None
            }
            _ => view.read_source(),
        })
    {
        return match wide {
            None => PointerOffsetTerm::scale_int32(native.into_owned(), byte_width),
            Some(unsigned) => {
                PointerOffsetTerm::scale_int64(native.into_owned(), byte_width, unsigned)
            }
        };
    }
    if wide == Some(false) {
        let widened = |v: MachineOperandView<'_>| match v.cast() {
            Some((MachineCastSpelling::Int64From32, _, _, child)) => {
                Some(child.retain(MachineIntegerType::Int32))
            }
            _ => None,
        };
        if u32::try_from(byte_width).is_ok()
            && let Some(child) = widened(view)
        {
            return transported_scaled_index(child, byte_width, None);
        }
        if let Some((MachineIntegerType::Int64, MachineBinaryOp::Multiply, [left, right])) =
            view.binary()
        {
            for (index, stride) in [(left, right), (right, left)] {
                if let (Some(index), Some(stride)) = (
                    widened(index),
                    stride.literal().and_then(|v| match v {
                        int64_constant!(v) => Some(crate::kernel::constant_i64(v)),
                        _ => None,
                    }),
                ) && let Ok(stride) = u32::try_from(stride)
                    && let Some(width) = i64::from(stride).checked_mul(byte_width)
                    && u32::try_from(width).is_ok()
                {
                    return transported_scaled_index(index, width, None);
                }
            }
        }
    }
    if wide.is_none()
        && let Some(v) = view.word32_constant()
    {
        return PointerOffsetTerm::Constant(i64::from(v as i32) * byte_width);
    }
    let constant = match wide {
        Some(true) => view.uint64_constant().and_then(|v| i64::try_from(v).ok()),
        Some(false) => view.int64_constant(),
        None => None,
    }
    .and_then(|v| v.checked_mul(byte_width));
    if let Some(constant) = constant {
        return PointerOffsetTerm::Constant(constant);
    }
    // The existing offset representation observes both signed and unsigned
    // wide indices through its Int64 carrier; `unsigned` carries the reading.
    let value = view.retain(if wide.is_some() {
        MachineIntegerType::Int64
    } else {
        MachineIntegerType::Int32
    });
    match wide {
        None => PointerOffsetTerm::Int32Scaled { value, byte_width },
        Some(unsigned) => PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, VerificationSession};

    #[test]
    fn common_call_indices_keep_roots_and_original_read_states() {
        use crate::kernel::{KernelTermImport, PureFunctionArgument, SharedPureApplication};
        let _session = VerificationSession::enter();
        let before =
            crate::kernel::intern_memory(Memory::new().with_block("call-retained_state", 8));
        let address = Memory::global_pointer("call-retained_state");
        let after = before
            .memory()
            .clone()
            .store(address.clone(), ProgramValue::Int32(7u32.into()));
        let application = SharedPureApplication::intern(
            "state_call".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                MachineTerm::MemoryLoad(before.clone(), address.into(), LoadKind::Int32),
            ))],
        );
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let root = KernelTermImport::default().machine_call(format, &application);
            let value = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
            let exports = KernelTermExport::machine_export_count();
            let framed = transport_framed_index(&value, &after, None).unwrap();
            assert_eq!(framed.shared_operand(), Some(&root));
            let normalized = normalize_exact_index(&value, &PureFactContext::new()).unwrap();
            assert_eq!(normalized.shared_operand(), Some(&root));
            let wide = (format != MachineIntegerType::Int32)
                .then_some(format == MachineIntegerType::UInt64);
            let offset = transported_scaled_index(framed, 4, wide);
            let (PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. }) = offset
            else {
                panic!("retained scaled call");
            };
            assert_eq!(
                value.shared_operand(),
                Some(&root.with_machine_observation_type(if wide.is_some() {
                    MachineIntegerType::Int64
                } else {
                    MachineIntegerType::Int32
                }))
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    fn retained(ty: MachineIntegerType, term: &MachineTerm) -> SharedMachineIntegerTerm {
        let root = KernelTerm::retained_machine_operand(ty, MachineOperandView::Legacy(term));
        SharedMachineIntegerTerm::from_shared(ty, root).unwrap()
    }

    fn normalization_parity(ty: MachineIntegerType, term: &MachineTerm, facts: &PureFactContext) {
        let value = retained(ty, term);
        let expected = normalize_exact_memory_loads_in_bitvector(value.structural_value(), facts);
        let exports = KernelTermExport::machine_export_count();
        let actual = normalize_exact_index(&value, facts).unwrap();
        assert_eq!(exports, KernelTermExport::machine_export_count());
        assert_eq!(
            actual.structural_value(),
            retained(ty, &expected).structural_value(),
            "{term:?}"
        );
        for width in [1, 4, -1] {
            let offset = if matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::UInt32) {
                PointerOffsetTerm::Int32Scaled {
                    value: value.clone(),
                    byte_width: width,
                }
            } else {
                PointerOffsetTerm::Int64Scaled {
                    value: value.clone(),
                    byte_width: width,
                    unsigned: ty == MachineIntegerType::UInt64,
                }
            };
            let native = match &offset {
                PointerOffsetTerm::Int32Scaled { .. } => match expected.as_const() {
                    Some(bits) => PointerOffsetTerm::Constant(i64::from(bits as i32) * width),
                    None => PointerOffsetTerm::Int32Scaled {
                        value: retained(ty, &expected),
                        byte_width: width,
                    },
                },
                _ => PointerOffsetTerm::scale_int64(
                    expected.clone(),
                    width,
                    ty == MachineIntegerType::UInt64,
                ),
            };
            let exports = KernelTermExport::machine_export_count();
            let actual = normalize_exact_memory_loads_in_pointer_offset(&offset, facts);
            assert_eq!(exports, KernelTermExport::machine_export_count());
            match (actual, native) {
                (
                    PointerOffsetTerm::Int32Scaled {
                        value: a,
                        byte_width: aw,
                    },
                    PointerOffsetTerm::Int32Scaled {
                        value: b,
                        byte_width: bw,
                    },
                ) => {
                    assert_eq!((aw, a.ty()), (bw, b.ty()));
                    assert_eq!(
                        a.structural_value(),
                        retained(b.ty(), b.structural_value()).structural_value()
                    );
                }
                (
                    PointerOffsetTerm::Int64Scaled {
                        value: a,
                        byte_width: aw,
                        unsigned: au,
                    },
                    PointerOffsetTerm::Int64Scaled {
                        value: b,
                        byte_width: bw,
                        unsigned: bu,
                    },
                ) => {
                    assert_eq!((aw, au, a.ty()), (bw, bu, b.ty()));
                    assert_eq!(
                        a.structural_value(),
                        retained(b.ty(), b.structural_value()).structural_value()
                    );
                }
                (a, b) => assert_eq!(a, b),
            }
        }
    }

    fn parity(
        ty: MachineIntegerType,
        term: &MachineTerm,
        after: &Memory,
        facts: Option<(&PureFactContext, bool)>,
    ) {
        let empty = PureFactContext::new();
        normalization_parity(ty, term, facts.map(|(facts, _)| facts).unwrap_or(&empty));
        let value = retained(ty, term);
        let before = KernelTermExport::machine_export_count();
        let result = transport_framed_index(&value, after, facts);
        assert_eq!(before, KernelTermExport::machine_export_count());
        // Deref on the old offset path read the structural operand, including
        // registered names already imported as read descriptors.
        let expected = transport_framed_atomic_bitvector(value.structural_value(), after, facts);
        assert_eq!(result.is_some(), expected.is_some(), "{term:?}");
        if let (Some(result), Some(expected)) = (result, expected) {
            assert_eq!(
                result.structural_value(),
                retained(ty, &expected).structural_value(),
                "{term:?}"
            );
            for width in [-4, 0, 1, 4] {
                let wide = match ty {
                    MachineIntegerType::Int32 => None,
                    MachineIntegerType::Int64 => Some(false),
                    MachineIntegerType::UInt64 => Some(true),
                    _ => continue,
                };
                let exports = KernelTermExport::machine_export_count();
                let offset = transported_scaled_index(result.clone(), width, wide);
                assert_eq!(exports, KernelTermExport::machine_export_count());
                let expected_offset = match wide {
                    None => PointerOffsetTerm::scale_int32(expected.clone(), width),
                    Some(unsigned) => {
                        PointerOffsetTerm::scale_int64(expected.clone(), width, unsigned)
                    }
                };
                match (&offset, &expected_offset) {
                    (
                        PointerOffsetTerm::Int32Scaled {
                            value: a,
                            byte_width: aw,
                        },
                        PointerOffsetTerm::Int32Scaled {
                            value: b,
                            byte_width: bw,
                        },
                    ) => {
                        assert_eq!(aw, bw);
                        assert_eq!(a.ty(), b.ty());
                        assert_eq!(a.structural_value(), b.structural_value(), "{term:?}");
                    }
                    (
                        PointerOffsetTerm::Int64Scaled {
                            value: a,
                            byte_width: aw,
                            unsigned: au,
                        },
                        PointerOffsetTerm::Int64Scaled {
                            value: b,
                            byte_width: bw,
                            unsigned: bu,
                        },
                    ) => {
                        assert_eq!((aw, au, a.ty()), (bw, bu, b.ty()));
                        assert_eq!(a.structural_value(), b.structural_value(), "{term:?}");
                    }
                    _ => assert_eq!(offset, expected_offset, "{term:?}, stride {width}"),
                }
            }
        }
    }

    #[test]
    fn framed_index_transport_preserves_native_constructor_rules() {
        let _session = VerificationSession::enter();
        let after = Memory::new();
        let x = MachineTerm::Variable(Variable(1018901));
        for ty in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let constants: Vec<_> = [0, 1, 3]
                .map(|v| {
                    ty.constant_term(
                        crate::kernel::MachineIntegerConstant::from_bits(ty.format(), v).unwrap(),
                    )
                    .unwrap()
                })
                .into_iter()
                .collect();
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::ShiftLeft,
            ] {
                for a in std::iter::once(&x).chain(constants.iter()) {
                    for b in std::iter::once(&x).chain(constants.iter()) {
                        let term = MachineTerm::Binary {
                            format: ty,
                            op,
                            left: Box::new(a.clone()),
                            right: Box::new(b.clone()),
                        };
                        parity(ty, &term, &after, None);
                    }
                }
            }
        }
        for (spelling, source, destination) in [
            (
                MachineCastSpelling::Int64From32,
                MachineIntegerType::Int32,
                MachineIntegerType::Int64,
            ),
            (
                MachineCastSpelling::UInt64From32,
                MachineIntegerType::UInt32,
                MachineIntegerType::UInt64,
            ),
            (
                MachineCastSpelling::Generic,
                MachineIntegerType::Int32,
                MachineIntegerType::UInt64,
            ),
        ] {
            for operand in [
                x.clone(),
                MachineTerm::constant(3),
                MachineTerm::add(x.clone(), x.clone()),
            ] {
                let term = MachineTerm::Cast {
                    spelling,
                    from: source,
                    to: destination,
                    value: Box::new(operand),
                };
                parity(destination, &term, &after, None);
                parity(
                    destination,
                    &MachineTerm::Binary {
                        format: destination,
                        op: MachineBinaryOp::Multiply,
                        left: Box::new(term),
                        right: Box::new(MachineTerm::int64_constant(4)),
                    },
                    &after,
                    None,
                );
            }
        }
    }

    #[test]
    fn framed_index_transport_retains_read_authority_at_each_state() {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: "transport-index".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = Memory::new().with_block("transport-index", 16).store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        );
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(before.clone()),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let term = MachineTerm::add(load.clone(), load.clone());
        let facts = PureFactContext::new();
        for after in [
            before.clone(),
            before.clone().store(
                pointer.offset_by_bytes(8),
                ProgramValue::Int32(MachineTerm::constant(9)),
            ),
            before.clone().store(
                pointer.clone(),
                ProgramValue::Int32(MachineTerm::constant(9)),
            ),
            before.clone().with_loop_memory_havoc_preserving_loans(
                Variable(1018911),
                &BTreeSet::new(),
                None,
                None,
            ),
            Memory::new(),
        ] {
            for policy in [None, Some((&facts, true)), Some((&facts, false))] {
                parity(MachineIntegerType::Int32, &term, &after, policy);
            }
        }
        let unchanged = transport_framed_index(
            &retained(MachineIntegerType::Int32, &term),
            &Memory::new(),
            None,
        )
        .unwrap();
        assert_eq!(unchanged.structural_value(), &term);
    }

    #[test]
    fn framed_index_transport_moves_registered_read_variables() {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: "registered-index".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = Memory::new().with_block("registered-index", 16);
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(before.clone()),
            Box::new(pointer.clone()),
            LoadKind::Int32,
        );
        let (variable, _) = crate::kernel::eval::load_variable_for_term(&load).unwrap();
        let term = MachineTerm::add(
            MachineTerm::Variable(variable),
            MachineTerm::Variable(variable),
        );
        let after = before.clone().store(
            pointer.offset_by_bytes(8),
            ProgramValue::Int32(MachineTerm::constant(9)),
        );
        let facts = PureFactContext::new();
        parity(
            MachineIntegerType::Int32,
            &term,
            &after,
            Some((&facts, true)),
        );
    }

    #[test]
    fn framed_index_transport_keeps_opaque_refusals() {
        let _session = VerificationSession::enter();
        let term = MachineTerm::If {
            condition: Box::new(ConditionTerm::Constant(true)),
            then_term: Box::new(MachineTerm::constant(1)),
            else_term: Box::new(MachineTerm::constant(2)),
        };
        let term = MachineTerm::add(term, MachineTerm::Variable(Variable(1018902)));
        parity(MachineIntegerType::Int32, &term, &Memory::new(), None);
        assert!(
            transport_framed_index(
                &retained(MachineIntegerType::Int32, &term),
                &Memory::new(),
                None
            )
            .is_none()
        );
    }

    #[test]
    fn framed_index_transport_keeps_opaque_constant_readings() {
        let _session = VerificationSession::enter();
        let after = Memory::new();
        let null = MachineTerm::PointerAddress(
            Box::new(Pointer::null()),
            crate::kernel::AddressObjectClass::NONE,
        );
        let x = MachineTerm::Variable(Variable(1018912));
        for ty in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            let one = if ty == MachineIntegerType::Int64 {
                MachineTerm::int64_constant(1)
            } else {
                MachineTerm::uint64_constant(1)
            };
            let compound = MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Add,
                left: Box::new(x.clone()),
                right: Box::new(x.clone()),
            };
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
            ] {
                for other in [one.clone(), compound.clone()] {
                    parity(
                        ty,
                        &MachineTerm::Binary {
                            format: ty,
                            op,
                            left: Box::new(null.clone()),
                            right: Box::new(other.clone()),
                        },
                        &after,
                        None,
                    );
                    parity(
                        ty,
                        &MachineTerm::Binary {
                            format: ty,
                            op,
                            left: Box::new(other),
                            right: Box::new(null.clone()),
                        },
                        &after,
                        None,
                    );
                }
            }
        }
    }

    #[test]
    fn exact_index_normalization_preserves_nested_smart_constructors() {
        let _session = VerificationSession::enter();
        let facts = PureFactContext::new();
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let c = |v| {
                ty.constant_term(
                    crate::kernel::MachineIntegerConstant::from_bits(ty.format(), v).unwrap(),
                )
                .unwrap()
            };
            let x = MachineTerm::Variable(Variable(1018960));
            let y = MachineTerm::Variable(Variable(1018961));
            let compound = MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Add,
                left: x.clone().into(),
                right: y.clone().into(),
            };
            let opaque = MachineTerm::If {
                condition: ConditionTerm::Variable(Variable(1018962)).into(),
                then_term: x.clone().into(),
                else_term: y.clone().into(),
            };
            let xor = MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::BitwiseXor,
                left: compound.clone().into(),
                right: opaque.clone().into(),
            };
            let difference = MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Subtract,
                left: compound.clone().into(),
                right: x.clone().into(),
            };
            let negative = MachineTerm::Binary {
                format: ty,
                op: MachineBinaryOp::Subtract,
                left: c(0).into(),
                right: x.clone().into(),
            };
            let cast = MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: MachineIntegerType::Int32,
                to: ty,
                value: MachineTerm::Variable(Variable(1018963)).into(),
            };
            let other_cast = MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                from: MachineIntegerType::UInt64,
                to: ty,
                value: MachineTerm::Variable(Variable(1018959)).into(),
            };
            let operands = [
                other_cast,
                x,
                compound,
                opaque,
                xor,
                difference,
                negative,
                cast,
                c(0),
                c(1),
                c(3),
                c(0xffff_ffff),
            ];
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
            ] {
                for a in &operands {
                    for b in &operands {
                        normalization_parity(
                            ty,
                            &MachineTerm::Binary {
                                format: ty,
                                op,
                                left: a.clone().into(),
                                right: b.clone().into(),
                            },
                            &facts,
                        );
                    }
                }
            }
            for operand in operands {
                let unary = MachineTerm::Unary {
                    format: ty,
                    op: crate::kernel::MachineUnaryOp::BitwiseNot,
                    operand: operand.into(),
                };
                normalization_parity(ty, &unary, &facts);
                normalization_parity(
                    ty,
                    &MachineTerm::Unary {
                        format: ty,
                        op: crate::kernel::MachineUnaryOp::BitwiseNot,
                        operand: unary.into(),
                    },
                    &facts,
                );
            }
        }
    }

    #[test]
    fn exact_index_normalization_keeps_state_kind_and_context_authority() {
        let _session = VerificationSession::enter();
        let pointer = Memory::global_pointer("exact-index");
        let initial = Memory::new().with_block("exact-index", 16);
        let stored = initial.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        );
        let empty = PureFactContext::new();
        for memory in [
            initial.clone(),
            stored.clone(),
            stored.clone().store(
                pointer.offset_by_bytes(8),
                ProgramValue::Int32(MachineTerm::constant(9)),
            ),
            stored.clone().store(
                pointer.clone(),
                ProgramValue::Int32(MachineTerm::constant(9)),
            ),
            stored.with_loop_memory_havoc_preserving_loans(
                Variable(1018950),
                &BTreeSet::new(),
                None,
                None,
            ),
        ] {
            for kind in [LoadKind::Int32, LoadKind::UInt32, LoadKind::UInt8] {
                let load = MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(memory.clone()),
                    Box::new(pointer.clone()),
                    kind,
                );
                for term in [
                    load.clone(),
                    MachineTerm::add(load.clone(), load.clone()),
                    MachineTerm::If {
                        condition: ConditionTerm::Variable(Variable(1018951)).into(),
                        then_term: load.clone().into(),
                        else_term: MachineTerm::constant(3).into(),
                    },
                    MachineTerm::PureFunctionApplication {
                        name: "exact-index-function".into(),
                        arguments: vec![load.clone()],
                    },
                ] {
                    normalization_parity(MachineIntegerType::Int32, &term, &empty);
                }
            }
        }
        let index = MachineTerm::Variable(Variable(1018953));
        let query = Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::scaled_int32_node(index.clone(), 4),
        };
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(
                initial.store(pointer, ProgramValue::Int32(MachineTerm::constant(5))),
            ),
            Box::new(query),
            LoadKind::Int32,
        );
        let value = retained(
            MachineIntegerType::Int32,
            &MachineTerm::add(load.clone(), load),
        );
        let parent = normalize_exact_index(&value, &empty).unwrap();
        let child = empty
            .clone()
            .assume_condition(ConditionTerm::equal(index, MachineTerm::constant(0)), true);
        normalization_parity(MachineIntegerType::Int32, value.structural_value(), &child);
        assert_eq!(
            normalize_exact_index(&value, &child)
                .unwrap()
                .operand_view()
                .word32_constant(),
            Some(10)
        );
        assert_eq!(
            normalize_exact_index(&value, &empty)
                .unwrap()
                .structural_value(),
            parent.structural_value()
        );
    }

    #[test]
    fn unchanged_opaque_guards_preserve_exact_pointer_index_identity() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let value = retained(
            ty,
            &MachineTerm::If {
                condition: Box::new(ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(1007510)),
                    Pointer::symbolic(Variable(1007511)),
                )),
                then_term: Box::new(MachineTerm::constant(1)),
                else_term: Box::new(MachineTerm::constant(0)),
            },
        );
        let empty = PureFactContext::new();
        let exports = KernelTermExport::machine_export_count();
        for _ in 0..8 {
            assert_eq!(normalize_exact_index(&value, &empty), Some(value.clone()));
            assert_eq!(
                transport_framed_index(&value, &Memory::new(), None),
                Some(value.clone())
            );
        }
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }

    mod scaling_tests {
        use super::*;
        include!("../../scaling_tests/kernel/memory_provenance/shared_index_transport.rs");
    }
}
