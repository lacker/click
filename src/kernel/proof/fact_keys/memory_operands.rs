//! Interned state-blind operand keys. Child keys compare by identity,
//! so shared arithmetic never expands into recursive boxed index keys.
use super::*;
use std::sync::{Mutex, OnceLock};

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum Node {
    Load(Box<MemoryErasedAddressKey>, LoadKind),
    Address(Box<MemoryErasedAddressKey>),
    Binary(
        BitvectorBinaryOp,
        MemoryErasedBitvectorKey,
        MemoryErasedBitvectorKey,
    ),
    Unary(BitvectorUnaryOp, MemoryErasedBitvectorKey),
    If(
        Box<MemoryErasedConditionKey>,
        MemoryErasedBitvectorKey,
        MemoryErasedBitvectorKey,
    ),
    Exact(OldMachineTerm),
    ExactOperand(crate::kernel::SharedMachineIntegerTerm),
}

struct Record {
    id: u64,
    fingerprint: u64,
    node: Node,
    checked_match: bool,
}
#[derive(Clone)]
pub(crate) struct MemoryErasedBitvectorKey(Arc<Record>);
impl fmt::Debug for MemoryErasedBitvectorKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("MemoryErasedBitvectorKey")
            .field(&self.0.id)
            .finish()
    }
}
impl PartialEq for MemoryErasedBitvectorKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.id == other.0.id
    }
}
impl Eq for MemoryErasedBitvectorKey {}
impl PartialOrd for MemoryErasedBitvectorKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for MemoryErasedBitvectorKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.id.cmp(&other.0.id)
    }
}
impl Hash for MemoryErasedBitvectorKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}
impl MemoryErasedBitvectorKey {
    pub(super) fn requires_checked_match(&self) -> bool {
        self.0.checked_match
    }
}

type Interner = HashMap<u64, Vec<Weak<Record>>>;
fn interner() -> &'static Mutex<Interner> {
    static INTERNER: OnceLock<Mutex<Interner>> = OnceLock::new();
    INTERNER.get_or_init(Mutex::default)
}
impl Drop for Record {
    fn drop(&mut self) {
        let Ok(mut table) = interner().try_lock() else {
            return;
        };
        if let Some(bucket) = table.get_mut(&self.fingerprint) {
            bucket.retain(|entry| entry.strong_count() != 0);
            if bucket.is_empty() {
                table.remove(&self.fingerprint);
            }
        }
    }
}
fn intern(node: Node) -> MemoryErasedBitvectorKey {
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT_ID: AtomicU64 = AtomicU64::new(1);
    crate::instrumentation::record_deterministic_work(1);
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    node.hash(&mut hash);
    let fingerprint = hash.finish();
    let mut table = interner().lock().expect("retained_state operand interner");
    let bucket = table.entry(fingerprint).or_default();
    let found = bucket
        .iter()
        .filter_map(Weak::upgrade)
        .find(|record| record.node == node);
    if let Some(record) = found {
        return MemoryErasedBitvectorKey(record);
    }
    bucket.retain(|entry| entry.strong_count() != 0);
    let checked_match = match &node {
        Node::Load(..) | Node::Address(..) => true,
        Node::Binary(_, a, b) => a.requires_checked_match() || b.requires_checked_match(),
        Node::Unary(_, a) => a.requires_checked_match(),
        Node::If(c, a, b) => {
            c.requires_checked_match() || a.requires_checked_match() || b.requires_checked_match()
        }
        Node::Exact(_) | Node::ExactOperand(_) => false,
    };
    let record = Arc::new(Record {
        id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
        fingerprint,
        node,
        checked_match,
    });
    bucket.push(Arc::downgrade(&record));
    MemoryErasedBitvectorKey(record)
}

pub(super) fn written(term: &OldMachineTerm) -> MemoryErasedBitvectorKey {
    // Conversions remain exact opaque keys, with the same identity on both
    // sides of the native/shared boundary. Import without evaluating the call.
    if let Some(root) =
        crate::kernel::KernelTermImport::default().float_to_machine(MachineIntegerType::Int32, term)
    {
        return operand(crate::kernel::MachineOperandView::Shared(&root));
    }
    let node = match term {
        OldMachineTerm::IntegerAddress(pointer, _) => {
            Node::Address(Box::new(memory_erased_address_key(pointer)))
        }
        OldMachineTerm::MemoryLoad(_, pointer, kind) => {
            Node::Load(Box::new(memory_erased_address_key(pointer)), *kind)
        }
        OldMachineTerm::Variable(variable) if crate::kernel::is_load_variable(variable) => {
            match (
                crate::kernel::registered_load_for_variable(variable),
                crate::kernel::registered_load_kind_for_variable(variable),
            ) {
                (Some((_, pointer)), Some(kind)) => {
                    Node::Load(Box::new(memory_erased_address_key(&pointer)), kind)
                }
                _ => Node::Exact(term.clone()),
            }
        }
        // Keep the existing opaque If boundary for Integer and Bool
        // predicates; only top-level machine observations have a key view.
        OldMachineTerm::If {
            condition,
            then_term,
            else_term,
        } if !matches!(
            condition.as_ref(),
            crate::kernel::integer_comparison_condition!(_, _)
        ) && !condition.is_bool_value_form() =>
        {
            Node::If(
                Box::new(memory_erased_boolean_operand_key(
                    crate::kernel::BooleanOperandView::Native(condition),
                )),
                memory_erased_bitvector_key(then_term),
                memory_erased_bitvector_key(else_term),
            )
        }
        OldMachineTerm::If { .. }
        | OldMachineTerm::RangeFold { .. }
        | OldMachineTerm::AlgebraicMatch { .. } => {
            Node::ExactOperand(crate::kernel::SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                term.clone(),
            ))
        }
        term => {
            if let Some((operator, left, right)) = term.as_binary() {
                Node::Binary(
                    operator,
                    memory_erased_bitvector_key(left),
                    memory_erased_bitvector_key(right),
                )
            } else if let Some((operator, value)) = term.as_unary() {
                Node::Unary(operator, memory_erased_bitvector_key(value))
            } else {
                Node::Exact(term.clone())
            }
        }
    };
    intern(node)
}

thread_local! {
    static SHARED_KEYS: std::cell::RefCell<HashMap<u64, MemoryErasedBitvectorKey>> = Default::default();
}

pub(super) fn clear() {
    SHARED_KEYS.with(|memo| memo.borrow_mut().clear());
}

pub(super) fn operand(view: crate::kernel::MachineOperandView<'_>) -> MemoryErasedBitvectorKey {
    use crate::kernel::{KernelTermNode, MachineOperandView as V};
    let V::Shared(root) = view else {
        let V::Old(term) = view else { unreachable!() };
        return written(term);
    };
    let get = |root: &crate::kernel::KernelTerm| {
        SHARED_KEYS.with(|memo| memo.borrow().get(&root.id()).cloned())
    };
    let mut pending = vec![(root.clone(), false)];
    while let Some((root, finish)) = pending.pop() {
        if get(&root).is_some() {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        let view = V::Shared(&root);
        // Retained inputs are keyed by written() below. Their children belong
        // to the native expression and have no shared IDs to schedule here.
        let children = if root.retained_machine_input().is_some() {
            Vec::new()
        } else if let Some((_, _, children)) = view.binary() {
            children.into_iter().collect::<Vec<_>>()
        } else if let Some((_, _, _, child)) = view.cast() {
            vec![child]
        } else if let Some((_, _, child)) = view.unary() {
            vec![child]
        } else if let Some((_, children)) = view.conditional_view() {
            children.into_iter().collect()
        } else {
            Vec::new()
        };
        if !finish && !children.is_empty() {
            pending.push((root.clone(), true));
            for child in children.into_iter().rev() {
                let V::Shared(child) = child else {
                    unreachable!()
                };
                if get(child).is_none() {
                    pending.push((child.clone(), false));
                }
            }
            continue;
        }
        let child_key = |child| {
            let V::Shared(child) = child else {
                unreachable!()
            };
            get(child).expect("keyed child")
        };
        let key = if let KernelTermNode::MemoryLoad { address, kind, .. } = root.node() {
            // This is a candidate key. It forgets the read state and keeps
            // the exact address policy and load kind used by native keys.
            intern(Node::Load(
                Box::new(memory_erased_address_key(
                    address.written().expect("retained read address"),
                )),
                *kind,
            ))
        } else if matches!(
            root.node(),
            crate::kernel::KernelTermNode::Fold(_)
                | crate::kernel::KernelTermNode::Match(_)
                | crate::kernel::KernelTermNode::FloatConvert { .. }
        ) {
            intern(Node::ExactOperand(
                crate::kernel::SharedMachineIntegerTerm::observe_shared(
                    MachineIntegerType::Int32,
                    root.with_machine_observation_type(MachineIntegerType::Int32),
                )
                .expect("machine fold"),
            ))
        } else if let Some(value) = root
            .machine_conversion_leaf()
            .or_else(|| root.written_machine_input())
        {
            written(value)
        } else if let Some(variable) = view.variable() {
            written(&OldMachineTerm::Variable(*variable))
        } else if let Some(literal) = view.literal() {
            intern(Node::Exact(literal))
        } else if let Some((format, op, [a, b])) = view.binary() {
            intern(Node::Binary(
                BitvectorBinaryOp::Machine(format, op),
                child_key(a),
                child_key(b),
            ))
        } else if let Some((encoding, source, destination, child)) = view.cast() {
            intern(Node::Unary(
                encoding.unary(source, destination),
                child_key(child),
            ))
        } else if let Some((format, op, child)) = view.unary() {
            intern(Node::Unary(
                BitvectorUnaryOp::Machine(format, op),
                child_key(child),
            ))
        } else if let Some((condition, [left, right])) = view.conditional_view() {
            if condition.is_integer_comparison() || condition.is_bool_value_form() {
                intern(Node::ExactOperand(
                    crate::kernel::SharedMachineIntegerTerm::observe_shared(
                        MachineIntegerType::Int32,
                        root.with_machine_observation_type(MachineIntegerType::Int32),
                    )
                    .expect("conditional observation"),
                ))
            } else {
                intern(Node::If(
                    Box::new(memory_erased_boolean_operand_key(condition)),
                    child_key(left),
                    child_key(right),
                ))
            }
        } else {
            unreachable!("shared machine operand fragment")
        };
        SHARED_KEYS.with(|memo| memo.borrow_mut().insert(root.id(), key));
    }
    get(root).expect("keyed root")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        KernelTerm, KernelTermExport, KernelTermImport, KernelTermNode, KernelType,
        MachineBinaryOp, MachineOperandView as V, ProgramPoint,
    };

    #[test]
    fn float_conversion_state_keys_are_exact_across_observation_widths() {
        let _session = crate::kernel::VerificationSession::enter();
        for name in ["c_float32_to_int32", "c_float32_to_uint64"] {
            let native =
                OldMachineTerm::opaque_conversion(name, OldMachineTerm::Variable(Variable(998209)));
            let different =
                OldMachineTerm::opaque_conversion(name, OldMachineTerm::Variable(Variable(998210)));
            let expected = written(&native);
            assert_ne!(expected, written(&different));
            assert!(!expected.requires_checked_match());
            for format in crate::kernel::machine_integer::FORMATS {
                let root = KernelTermImport::default().machine(format, &native);
                let before = KernelTermExport::machine_export_count();
                assert_eq!(operand(V::Shared(&root)), expected);
                assert_eq!(KernelTermExport::machine_export_count(), before);
            }
        }
    }

    #[test]
    fn conditional_keys_preserve_guard_policy_and_shared_arms() {
        let _session = crate::kernel::VerificationSession::enter();
        for condition in [
            OldConditionTerm::Variable(Variable(998203)),
            OldConditionTerm::equal(
                OldMachineTerm::Variable(Variable(998204)),
                OldMachineTerm::constant(0),
            ),
            OldConditionTerm::IntegerEqual(
                crate::kernel::IntegerTerm::Variable(Variable(998205)).into(),
                crate::kernel::IntegerTerm::constant_i64(0).into(),
            ),
        ] {
            let native = OldMachineTerm::If {
                condition: Box::new(condition),
                then_term: Box::new(OldMachineTerm::Variable(Variable(998206))),
                else_term: Box::new(OldMachineTerm::constant(1)),
            };
            for format in crate::kernel::machine_integer::FORMATS {
                let shared = KernelTermImport::default().machine(format, &native);
                let expected = written(&native);
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(operand(V::Shared(&shared)), expected, "{format:?}");
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }

    #[test]
    fn shared_state_operand_keys_match_written_structure_without_export() {
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                MachineBinaryOp::Add,
                MachineBinaryOp::Subtract,
                MachineBinaryOp::Multiply,
                MachineBinaryOp::Divide,
                MachineBinaryOp::Remainder,
                MachineBinaryOp::BitwiseAnd,
                MachineBinaryOp::BitwiseOr,
                MachineBinaryOp::BitwiseXor,
                MachineBinaryOp::ShiftLeft,
                MachineBinaryOp::ShiftRight,
            ] {
                let native = OldMachineTerm::Binary {
                    format,
                    op,
                    left: Box::new(OldMachineTerm::Variable(Variable(998201))),
                    right: Box::new(OldMachineTerm::Variable(Variable(998202))),
                };
                let shared = KernelTermImport::default()
                    .machine_arithmetic(format, &native)
                    .unwrap();
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(operand(V::Shared(&shared)), written(&native));
                assert!(!operand(V::Shared(&shared)).requires_checked_match());
                assert_eq!(KernelTermExport::machine_export_count(), exports);
            }
        }
    }

    #[test]
    fn retained_read_candidate_keys_keep_kind_and_do_not_build_a_native_load() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Address::symbolic(Variable(998203));
        let before = crate::kernel::intern_memory(crate::kernel::SymbolicMemory::new());
        let after = crate::kernel::intern_memory(before.memory().clone().store(
            address.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        ));
        let source = |memory: &SharedMemory, kind| {
            OldMachineTerm::read_named(ProgramPoint::at(memory), Box::new(address.clone()), kind)
        };
        let before_read = source(&before, LoadKind::Int32);
        let after_read = source(&after, LoadKind::Int32);
        let other_kind = source(&after, LoadKind::UInt32);
        let key = |read| {
            let root = KernelTermImport::default().machine(MachineIntegerType::Int32, read);
            assert!(matches!(root.node(), KernelTermNode::MemoryLoad { .. }));
            let retained = operand(V::Shared(&root));
            assert_eq!(retained, written(read));
            assert!(!root.has_cached_machine_leaf());
            retained
        };
        assert_eq!(key(&before_read), key(&after_read));
        assert_ne!(key(&after_read), key(&other_kind));
        let (name, _) = crate::kernel::eval::load_variable_for_term(&before_read).unwrap();
        assert_eq!(written(&OldMachineTerm::Variable(name)), key(&before_read));
    }

    #[test]
    fn exact_comparison_keys_preserve_truth_without_exporting_the_condition() {
        let _session = crate::kernel::VerificationSession::enter();
        let variables = |ty: KernelType| {
            [Variable(998241), Variable(998242)].map(|v| KernelTerm::variable(ty.clone(), v))
        };
        let integer = KernelTerm::integer_comparison(
            IntegerComparisonOperator::LessThan,
            variables(KernelType::Integer),
        )
        .unwrap();
        let boolean = KernelTerm::boolean_equal_raw(variables(KernelType::Bool));
        for root in [integer, boolean] {
            for truth in [false, true] {
                let condition =
                    crate::kernel::StoredConditionTerm::from_root(root.clone()).unwrap();
                let goal = Proposition::ConditionIs(condition, truth);
                let MemoryErasedPropositionKey::Exact(Proposition::ConditionIs(stored, polarity)) =
                    memory_erased_proposition_key(&goal)
                else {
                    panic!("comparison requires an exact key");
                };
                assert_eq!(stored.root(), Some(&root));
                assert_eq!(polarity, truth);
                assert!(root.cached_condition_output().is_none());
            }
        }
    }

    #[test]
    fn observation_keys_select_native_load_candidates_without_proving_them() {
        use crate::kernel::machine_integer::comparison::condition_for_operand_views;
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(
            crate::kernel::SymbolicMemory::new().with_block("retained_state-comparison", 4),
        );
        let pointer = Address::new(
            "retained_state-comparison".into(),
            AddressOffset::constant(0),
        );
        let variable = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            LoadKind::Int32,
            4,
            &memory,
        );
        let format = MachineIntegerType::Int32;
        let native = OldMachineTerm::Binary {
            format,
            op: MachineBinaryOp::Add,
            left: Box::new(OldMachineTerm::Variable(variable)),
            right: Box::new(OldMachineTerm::constant(1)),
        };
        let shared = KernelTermImport::default()
            .machine_arithmetic(format, &native)
            .unwrap();
        let limit = OldMachineTerm::constant(20);
        for relation in [
            CompareRelation::Equal,
            CompareRelation::LessThan,
            CompareRelation::LessEqual,
        ] {
            let native = Proposition::condition_is(
                OldConditionTerm::machine_compare(format, relation, native.clone(), limit.clone()),
                true,
            );
            let exports = KernelTermExport::machine_export_count();
            let shared = Proposition::condition_is(
                condition_for_operand_views(format, relation, [V::Shared(&shared), V::Old(&limit)]),
                true,
            );
            let key = memory_erased_proposition_key(&shared);
            assert_eq!(key, memory_erased_proposition_key(&native));
            assert!(key.requires_checked_match());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }

    #[test]
    fn state_operand_memo_tracks_restored_load_registries() {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = crate::kernel::eval::capture_load_variable_registry();
        let memory = crate::kernel::intern_memory(
            crate::kernel::SymbolicMemory::new().with_block("retained_state-key", 4),
        );
        let pointer = Address::new("retained_state-key".into(), AddressOffset::constant(0));
        let variable = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &pointer,
            LoadKind::Int32,
            4,
            &memory,
        );
        let loaded = crate::kernel::eval::capture_load_variable_registry();
        let shared = KernelTerm::variable(KernelType::Program(ProgramType::Int32), variable);
        let key = operand(V::Shared(&shared));
        assert!(key.requires_checked_match());
        assert_eq!(
            key,
            written(&OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&memory),
                Box::new(pointer),
                LoadKind::Int32
            ))
        );
        crate::kernel::eval::restore_load_variable_registry(&empty);
        let unregistered = operand(V::Shared(&shared));
        assert_ne!(key, unregistered);
        assert!(!unregistered.requires_checked_match());
        crate::kernel::eval::restore_load_variable_registry(&loaded);
        assert_eq!(key, operand(V::Shared(&shared)));
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/fact_keys/memory_operands/tests.rs");
}
