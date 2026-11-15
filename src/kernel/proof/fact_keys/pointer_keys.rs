//! Shallow offset keys retain shared graphs. These are identities/selectors,
//! not evidence; state erasure still requires the existing checked bridge.
use super::*;
use crate::kernel::{
    KernelPointerOffset as O, MachineOperandView as V, SharedPointerAddress, SharedPointerOffset,
    SharedPointerValue,
};
use std::sync::{Mutex, OnceLock};

type Table<N> = Mutex<HashMap<u64, Vec<Weak<Record<N>>>>>;
pub(crate) trait KeyNode: Eq + Hash + Sized + 'static {
    fn table() -> &'static Table<Self>;
    fn checked_match(&self) -> bool {
        false
    }
}
pub(crate) struct Record<N: KeyNode> {
    id: u64,
    fingerprint: u64,
    node: N,
    checked: bool,
}
pub(crate) struct Canonical<N: KeyNode>(Arc<Record<N>>);
impl<N: KeyNode> Clone for Canonical<N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<N: KeyNode> fmt::Debug for Canonical<N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PointerKey").field(&self.0.id).finish()
    }
}
impl<N: KeyNode> PartialEq for Canonical<N> {
    fn eq(&self, b: &Self) -> bool {
        self.0.id == b.0.id
    }
}
impl<N: KeyNode> Eq for Canonical<N> {}
impl<N: KeyNode> PartialOrd for Canonical<N> {
    fn partial_cmp(&self, b: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(b))
    }
}
impl<N: KeyNode> Ord for Canonical<N> {
    fn cmp(&self, b: &Self) -> std::cmp::Ordering {
        self.0.id.cmp(&b.0.id)
    }
}
impl<N: KeyNode> Hash for Canonical<N> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        // Some selectors retain only a fingerprint, not this key handle.
        // Keep that fingerprint stable after the last live key is dropped.
        self.0.fingerprint.hash(h)
    }
}
impl<N: KeyNode> Drop for Record<N> {
    fn drop(&mut self) {
        let Ok(mut table) = N::table().try_lock() else {
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
impl<N: KeyNode> Canonical<N> {
    pub(super) fn new(node: N) -> Self {
        use std::sync::atomic::{AtomicU64, Ordering};
        static NEXT: AtomicU64 = AtomicU64::new(1);
        crate::instrumentation::record_deterministic_work(1);
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        node.hash(&mut hash);
        let fingerprint = hash.finish();
        let mut table = N::table().lock().expect("pointer key interner");
        let bucket = table.entry(fingerprint).or_default();
        if let Some(record) = bucket
            .iter()
            .filter_map(Weak::upgrade)
            .find(|record| record.node == node)
        {
            return Self(record);
        }
        bucket.retain(|entry| entry.strong_count() != 0);
        let checked = node.checked_match();
        let record = Arc::new(Record {
            id: NEXT.fetch_add(1, Ordering::Relaxed),
            fingerprint,
            node,
            checked,
        });
        bucket.push(Arc::downgrade(&record));
        Self(record)
    }
    #[cfg(test)]
    pub(super) fn node(&self) -> &N {
        &self.0.node
    }
    pub(super) fn requires_checked_match(&self) -> bool {
        self.0.checked
    }
}
impl KeyNode for MemoryErasedPointerOffsetNode {
    fn table() -> &'static Table<Self> {
        static TABLE: OnceLock<Table<MemoryErasedPointerOffsetNode>> = OnceLock::new();
        TABLE.get_or_init(Default::default)
    }
    fn checked_match(&self) -> bool {
        self.requires_checked_match()
    }
}
impl KeyNode for AlphaPointerOffsetNode {
    fn table() -> &'static Table<Self> {
        static TABLE: OnceLock<Table<AlphaPointerOffsetNode>> = OnceLock::new();
        TABLE.get_or_init(Default::default)
    }
}
impl KeyNode for AlphaMachineKey {
    fn table() -> &'static Table<Self> {
        static TABLE: OnceLock<Table<AlphaMachineKey>> = OnceLock::new();
        TABLE.get_or_init(Default::default)
    }
}

/// The memo belongs to this one lexical scope, never to an ambient fact set.
fn offsets<K: Clone>(
    root: &SharedPointerOffset,
    mut build: impl FnMut(&O, Option<[K; 2]>) -> Option<K>,
) -> Option<K> {
    let mut memo: HashMap<SharedPointerOffset, K> = HashMap::new();
    let mut pending = vec![(root.clone(), false)];
    while let Some((offset, finish)) = pending.pop() {
        if memo.contains_key(&offset) {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        if let O::Add(children) = offset.node() {
            if !finish {
                pending.push((offset.clone(), true));
                pending.extend(children.iter().rev().cloned().map(|child| (child, false)));
                continue;
            }
        }
        let children = if let O::Add([a, b]) = offset.node() {
            Some([memo[a].clone(), memo[b].clone()])
        } else {
            None
        };
        let key = build(offset.node(), children)?;
        memo.insert(offset, key);
    }
    memo.remove(root)
}

#[allow(dead_code)] // Prepared before the pointer-producing boundaries switch.
pub(super) fn state_offset(root: &SharedPointerOffset) -> MemoryErasedPointerOffsetKey {
    offsets(root, |node, children| {
        Some(Canonical::new(match node {
            O::Constant(value) => {
                MemoryErasedPointerOffsetNode::Exact(PointerOffsetTerm::Constant(*value))
            }
            O::Variable(value) => {
                MemoryErasedPointerOffsetNode::Exact(PointerOffsetTerm::Variable(*value))
            }
            O::Add(_) => {
                let [a, b] = children.unwrap();
                MemoryErasedPointerOffsetNode::Add(a, b)
            }
            O::Int32Scaled { value, byte_width } => MemoryErasedPointerOffsetNode::Int32Scaled {
                value: memory_operands::operand(V::Shared(value)),
                byte_width: *byte_width,
            },
            O::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => MemoryErasedPointerOffsetNode::Int64Scaled {
                value: memory_operands::operand(V::Shared(value)),
                byte_width: *byte_width,
                unsigned: *unsigned,
            },
        }))
    })
    .expect("state key is total")
}

#[allow(dead_code)]
pub(super) fn alpha_offset<const ALLOW_LOADS: bool>(
    root: &SharedPointerOffset,
    bindings: &mut AlphaBindings,
    next: &mut usize,
) -> Option<AlphaPointerOffsetKey> {
    enum Frame {
        Visit(SharedPointerOffset),
        Add(SharedPointerOffset, usize),
    }
    // Registry definitions can contain local binders. Like the native load
    // memo, retain both the entry ordinal and the resulting ordinal.
    let mut memo: HashMap<(SharedPointerOffset, usize), (AlphaPointerOffsetKey, usize)> =
        HashMap::new();
    let mut numeric: HashMap<(u64, usize), Canonical<AlphaMachineKey>> = HashMap::new();
    let mut pending = vec![Frame::Visit(root.clone())];
    let mut values = Vec::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Add(offset, before) => {
                let b = values.pop()?;
                let a = values.pop()?;
                let key = Canonical::new(AlphaPointerOffsetNode::Add(a, b));
                memo.insert((offset, before), (key.clone(), *next));
                values.push(key);
            }
            Frame::Visit(offset) => {
                alpha_work_checkpoint(bindings, 1)?;
                let before = *next;
                if let Some((key, after)) = memo.get(&(offset.clone(), before)) {
                    *next = *after;
                    values.push(key.clone());
                    continue;
                }
                let node = match offset.node() {
                    O::Add([a, b]) => {
                        pending.push(Frame::Add(offset.clone(), before));
                        pending.push(Frame::Visit(b.clone()));
                        pending.push(Frame::Visit(a.clone()));
                        continue;
                    }
                    O::Constant(value) => AlphaPointerOffsetNode::Constant(*value),
                    O::Variable(variable) => {
                        let key = alpha_pointer_offset_key_with_bindings::<ALLOW_LOADS>(
                            &PointerOffsetTerm::Variable(*variable),
                            bindings,
                            next,
                        )?;
                        memo.insert((offset, before), (key.clone(), *next));
                        values.push(key);
                        continue;
                    }
                    O::Int32Scaled { value, byte_width }
                    | O::Int64Scaled {
                        value, byte_width, ..
                    } => {
                        let cache = (value.id(), *next);
                        let key = match numeric.get(&cache) {
                            Some(key) => key.clone(),
                            None => {
                                let key = Canonical::new(alpha_machine_key::<ALLOW_LOADS>(
                                    V::Shared(value),
                                    bindings,
                                    next,
                                )?);
                                numeric.insert(cache, key.clone());
                                key
                            }
                        };
                        match offset.node() {
                            O::Int64Scaled { unsigned, .. } => {
                                AlphaPointerOffsetNode::Int64Scaled {
                                    value: key,
                                    byte_width: *byte_width,
                                    unsigned: *unsigned,
                                }
                            }
                            _ => AlphaPointerOffsetNode::Int32Scaled {
                                value: key,
                                byte_width: *byte_width,
                            },
                        }
                    }
                };
                let key = Canonical::new(node);
                memo.insert((offset, before), (key.clone(), *next));
                values.push(key);
            }
        }
    }
    values.pop()
}

#[allow(dead_code)]
pub(super) fn state_address(pointer: &SharedPointerAddress) -> MemoryErasedPointerKey {
    let depth = POINTER_READ_KEY_DEPTH.with(|depth| depth.replace(depth.get() + 1));
    let _restore = PointerReadKeyDepth(depth);
    let block = pointer.node().block.native_atom();
    // Existing depth bound and registry authority; never export the offset.
    let read = match block {
        PointerBlock::LoadedPointer(_) if depth < 3 => Pointer {
            block: block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        }
        .as_loaded_value()
        .map(|read| read.defining_address),
        PointerBlock::Symbolic(variable) if depth < 3 => {
            crate::kernel::registered_load_for_variable(variable).map(|(_, source)| source)
        }
        _ => None,
    };
    MemoryErasedPointerKey {
        block: read
            .map(|source| {
                MemoryErasedPointerBlockKey::Read(Box::new(memory_erased_pointer_key(&source)))
            })
            .unwrap_or_else(|| MemoryErasedPointerBlockKey::Exact(block.clone())),
        offset: Box::new(state_offset(&pointer.node().offset)),
    }
}
#[allow(dead_code)]
pub(super) fn alpha_address<const ALLOW_LOADS: bool>(
    pointer: &SharedPointerAddress,
    bindings: &mut AlphaBindings,
    next: &mut usize,
) -> Option<AlphaPointerKey> {
    alpha_work_checkpoint(bindings, 1)?;
    Some(AlphaPointerKey {
        block: alpha_pointer_block_key::<ALLOW_LOADS>(
            pointer.node().block.native_atom(),
            bindings,
            next,
        )?,
        offset: alpha_offset::<ALLOW_LOADS>(&pointer.node().offset, bindings, next)?,
    })
}
#[allow(dead_code)]
pub(super) fn recorded_value(pointer: &SharedPointerValue) -> MemoryErasedPointerValueKey {
    let p = pointer.node();
    let q = p.qualifiers.as_ref();
    let known = q.is_some_and(|q| q.extent_known);
    MemoryErasedPointerValueKey {
        program_type: p.program_type,
        address: state_address(&p.address),
        designation: state_address(&p.designation),
        opaque_extent: if known {
            None
        } else {
            p.opaque_extent.as_ref().map(state_address)
        },
        extent: q.and_then(|q| q.extent.as_ref()).map(|e| {
            (
                state_address(&e.start),
                memory_operands::operand(V::Shared(&e.width)),
            )
        }),
        extent_known: known,
    }
}

#[allow(dead_code)]
pub(super) fn alpha_value<const ALLOW_LOADS: bool>(
    pointer: &SharedPointerValue,
    bindings: &mut AlphaBindings,
    next: &mut usize,
) -> Option<AlphaProgramValueKey> {
    alpha_work_checkpoint(bindings, 1)?;
    let p = pointer.node();
    let q = p.qualifiers.as_ref();
    let known = q.is_some_and(|q| q.extent_known);
    Some(AlphaProgramValueKey::Pointer {
        program_type: p.program_type,
        pointee_volatile: q.is_some_and(|q| q.volatile),
        pointee_constant: q.is_some_and(|q| q.constant),
        pointer: alpha_address::<ALLOW_LOADS>(&p.address, bindings, next)?,
        designation: alpha_address::<ALLOW_LOADS>(&p.designation, bindings, next)?,
        extent_known: known,
        opaque_extent: if known {
            None
        } else {
            match &p.opaque_extent {
                Some(p) => Some(alpha_address::<ALLOW_LOADS>(p, bindings, next)?),
                None => None,
            }
        },
        extent: match q.and_then(|q| q.extent.as_ref()) {
            Some(e) => Some((
                alpha_address::<ALLOW_LOADS>(&e.start, bindings, next)?,
                alpha_machine_key::<ALLOW_LOADS>(V::Shared(&e.width), bindings, next)?,
            )),
            None => None,
        },
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        KernelTermExport, MachineBinaryOp, SharedMachineIntegerTerm, SubobjectExtent,
        VerificationSession,
    };
    fn pointer(offset: PointerOffsetTerm) -> PointerValue {
        let address = Pointer {
            block: PointerBlock::Concrete("shared-key".into()),
            offset,
        };
        PointerValue::new(address.clone(), ProgramType::VoidPointer)
            .with_designation(Arc::new(address.clone()))
            .with_pointee_volatile(true)
            .with_pointee_constant(true)
            .with_extent(Some(SubobjectExtent {
                start: address,
                width: MachineTerm::Binary {
                    format: MachineIntegerType::Int32,
                    op: MachineBinaryOp::Add,
                    left: MachineTerm::Variable(Variable(1010002)).into(),
                    right: MachineTerm::constant(4).into(),
                },
            }))
            .with_opaque_extent(Some(Arc::new(Pointer::symbolic(Variable(1010001)))))
    }

    #[test]
    fn shared_keys_match_native_addresses_metadata_and_widths() {
        let _session = VerificationSession::enter();
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let scalar =
                SharedMachineIntegerTerm::index(ty, MachineTerm::Variable(Variable(1010003)));
            let scaled = if matches!(ty, MachineIntegerType::Int32 | MachineIntegerType::UInt32) {
                PointerOffsetTerm::Int32Scaled {
                    value: scalar,
                    byte_width: -4,
                }
            } else {
                PointerOffsetTerm::Int64Scaled {
                    value: scalar,
                    byte_width: 8,
                    unsigned: true,
                }
            };
            let source = pointer(PointerOffsetTerm::Add(
                Box::new(scaled),
                Box::new(PointerOffsetTerm::Constant(3)),
            ));
            let shared = SharedPointerValue::import(&source);
            let expected = memory_erased_pointer_value_key(&source);
            let alpha = alpha_program_value_key_with_bindings::<true>(
                &ProgramValue::Pointer(source.clone()),
                &mut fold_keys::bindings(),
                &mut 0,
            );
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(recorded_value(&shared), expected);
            assert_eq!(
                alpha_value::<true>(&shared, &mut fold_keys::bindings(), &mut 0),
                alpha
            );
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            // Exact custody remains separate from selector identity.
            let changed = source.clone().with_pointee_constant(false);
            let changed = SharedPointerValue::import(&changed);
            assert_ne!(shared, changed);
            assert_eq!(recorded_value(&shared), recorded_value(&changed));
            assert_ne!(
                alpha_value::<true>(&shared, &mut fold_keys::bindings(), &mut 0),
                alpha_value::<true>(&changed, &mut fold_keys::bindings(), &mut 0)
            );
        }
    }
    #[test]
    fn shared_state_selection_retains_checked_match_and_alpha_state_identity() {
        let _session = VerificationSession::enter();
        let address = crate::kernel::Memory::global_pointer("shared-key-load");
        let before = crate::kernel::Memory::new().with_block("shared-key-load", 16);
        let after = before.clone().store(
            address.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        );
        let make = |memory| {
            SharedPointerValue::import(&pointer(PointerOffsetTerm::Int32Scaled {
                value: SharedMachineIntegerTerm::index(
                    MachineIntegerType::Int32,
                    MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(memory),
                        Box::new(address.clone()),
                        LoadKind::Int32,
                    ),
                ),
                byte_width: 4,
            }))
        };
        let a = make(before);
        let b = make(after);
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(recorded_value(&a), recorded_value(&b));
        assert!(recorded_value(&a).requires_checked_match());
        assert_ne!(
            alpha_value::<true>(&a, &mut fold_keys::bindings(), &mut 0),
            alpha_value::<true>(&b, &mut fold_keys::bindings(), &mut 0)
        );
        let mut bindings = fold_keys::bindings();
        bindings.state_aware = false;
        assert!(alpha_value::<false>(&a, &mut bindings, &mut 0).is_none());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
    #[test]
    fn shared_address_keys_preserve_load_depth_and_logical_call_identity() {
        let _session = VerificationSession::enter();
        let memory = crate::kernel::intern_memory(crate::kernel::Memory::new());
        let mut source = Pointer::symbolic(Variable(1010200));
        for _ in 0..6 {
            source = Pointer::loaded_value(&memory, &source);
            let shared = SharedPointerAddress::import(&source);
            assert_eq!(state_address(&shared), memory_erased_pointer_key(&source));
            assert_eq!(
                alpha_address::<true>(&shared, &mut fold_keys::bindings(), &mut 0),
                alpha_pointer_key_with_bindings::<true>(
                    &source,
                    &mut fold_keys::bindings(),
                    &mut 0
                )
            );
        }
        let make = || {
            SharedPointerAddress::import(&Pointer {
                block: PointerBlock::PureFunctionApplication(
                    crate::kernel::SharedPureApplication::intern("pointer-key-call".into(), vec![]),
                ),
                offset: PointerOffsetTerm::Constant(0),
            })
        };
        let a = make();
        let b = make();
        assert_ne!(a, b);
        assert_eq!(state_address(&a), state_address(&b));
        assert_eq!(
            alpha_address::<true>(&a, &mut fold_keys::bindings(), &mut 0),
            alpha_address::<true>(&b, &mut fold_keys::bindings(), &mut 0)
        );
    }
    #[test]
    fn compact_key_fingerprints_survive_dropping_all_handles() {
        let fingerprint = || {
            let key = memory_erased_pointer_offset_key(&PointerOffsetTerm::Constant(1010301));
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            key.hash(&mut hasher);
            hasher.finish()
        };
        assert_eq!(fingerprint(), fingerprint());
    }
    #[test]
    fn shared_offset_binders_use_the_selected_scope() {
        let _session = VerificationSession::enter();
        let make = |v| O::Variable(Variable(v)).into_shared().unwrap();
        let a = make(1010101);
        let b = make(1010102);
        let mut left = fold_keys::bindings();
        left.bitvector.insert(Variable(1010101), 0);
        let mut right = fold_keys::bindings();
        right.bitvector.insert(Variable(1010102), 0);
        assert_eq!(
            alpha_offset::<true>(&a, &mut left, &mut 1),
            alpha_offset::<true>(&b, &mut right, &mut 1)
        );
        assert_ne!(
            alpha_offset::<true>(&a, &mut left, &mut 1),
            alpha_offset::<true>(&b, &mut left, &mut 1)
        );
    }
}
#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/kernel/proof/fact_keys/pointer_keys.rs");
}
