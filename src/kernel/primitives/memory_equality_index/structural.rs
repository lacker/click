//! Structural resource candidates, maintained with the resource input.
//! This derived index is part of the trusted kernel. Hashes and geometric
//! matches select occurrences; the existing judgments check every occurrence.
use super::super::resource_algebra::{insert_resource_index_entry, remove_resource_index_entry};
use super::*;
use crate::kernel::{bits32_constant, int64_constant};

type Key = (PointerBlock, u64);

#[derive(Clone, Debug, Default)]
pub(in crate::kernel::primitives) struct StructuralMemory {
    shapes: PersistentMap<Key, ResourceEntryIds>,
    origins: PersistentMap<Key, ResourceEntryIds>,
}

fn shape(pointer: &Pointer) -> Key {
    (
        pointer.block.clone(),
        crate::kernel::assumptions::memory_blind_pointer_fingerprint(pointer),
    )
}

fn origin(pointer: &Pointer) -> Option<Key> {
    // Literal bases need no normalization traversal (including during large
    // certified input publications).
    let offset = match &pointer.offset {
        PointerOffsetTerm::Constant(_) => AffineOffset::constant(0),
        offset => AffineOffset::of(offset)?,
    };
    Some((pointer.block.clone(), offset.origin_fingerprint()))
}

impl StructuralMemory {
    pub(in crate::kernel::primitives) fn update(
        &mut self,
        base: &Pointer,
        entry: ResourceEntryId,
        insert: bool,
    ) {
        let update = if insert {
            insert_resource_index_entry
        } else {
            remove_owned_key
        };
        self.shapes = update(&self.shapes, shape(base), entry);
        if let Some(key) = origin(base) {
            self.origins = update(&self.origins, key, entry);
        }
    }

    fn candidates(&self, pointer: &Pointer) -> BTreeSet<ResourceEntryId> {
        let mut result = BTreeSet::new();
        let mut add_shape = |offset: &PointerOffsetTerm| {
            let key = shape(&Pointer {
                block: pointer.block.clone(),
                offset: offset.clone(),
            });
            if let Some(entries) = self.shapes.get(&key) {
                result.extend(entries.iter().copied());
            }
        };
        add_shape(&pointer.offset);
        // These are subterms of the explicit access, not alternate spellings
        // of it. They cover precisely the bases the structural read judgment
        // can recognize in an addition, including either operand.
        if let PointerOffsetTerm::Add(left, right) = &pointer.offset {
            add_shape(left);
            add_shape(right);
        }
        if let Some(key) = origin(pointer)
            && let Some(entries) = self.origins.get(&key)
        {
            result.extend(entries.iter().copied());
        }
        result
    }
}

fn remove_owned_key(
    index: &PersistentMap<Key, ResourceEntryIds>,
    key: Key,
    entry: ResourceEntryId,
) -> PersistentMap<Key, ResourceEntryIds> {
    remove_resource_index_entry(index, &key, entry)
}

// The raw interval summary can decide an access at a plain origin plus a
// constant displacement. Symbolic indexing and state matching need the
// shape payload instead; their membership is a checked judgment, not an
// ordering of affine vectors.
fn plain_origin(mut offset: &PointerOffsetTerm) -> bool {
    loop {
        match offset {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => return true,
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => {
                let value = value.operand_view();
                return value.variable().is_some()
                    || value.literal().is_some_and(|literal| {
                        matches!(literal, bits32_constant!(_) | int64_constant!(_))
                    });
            }
            PointerOffsetTerm::Add(left, right) => {
                offset = if matches!(left.as_ref(), PointerOffsetTerm::Constant(_)) {
                    right
                } else if matches!(right.as_ref(), PointerOffsetTerm::Constant(_)) {
                    left
                } else {
                    return false;
                };
            }
        }
    }
}

impl ResourceContext {
    pub(in crate::kernel::primitives) fn structural_memory_entries(
        &self,
        base: &Pointer,
        start: &Pointer,
        bytes: Option<u32>,
    ) -> MemoryAccessEntries {
        if let Some(bytes) = bytes
            && plain_origin(&start.offset)
            && let Some(offset) = AffineOffset::of(&start.offset)
            && let Some(bucket) = self
                .storage
                .index
                .memory_addresses
                .classes
                .get(&start.block)
            && bucket.general_coordinates == 0
            && bucket.read_intervals.len() == bucket.memory_count
            && let Some(end) = offset.checked_add(&AffineOffset::constant(i128::from(bytes)))
        {
            return MemoryAccessEntries::Intervals(
                bucket
                    .read_intervals
                    .covering(&AddressCoordinate(offset), &AddressCoordinate(end)),
            );
        }
        MemoryAccessEntries::Structural(
            self.storage
                .index
                .structural_memory
                .candidates(base)
                .into_iter(),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn structural_selection_preserves_width_forks_and_consumption() {
        let base = Pointer::symbolic(Variable(873_000));
        let owner =
            ResourceFact::own_memory(MemoryRange::new(base.clone(), 0u32.into(), 4u32.into()));
        let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let empty = PureFactContext::new();
        let partial = ResourceFact::view_memory(MemoryRange::new(
            base.offset_by_bytes(4),
            0u32.into(),
            1u32.into(),
        ));
        assert!(resources.satisfies_memory_fact_structurally(&partial));
        let removed = resources
            .clone()
            .without_exact_representation(&owner)
            .unwrap();
        assert!(!removed.satisfies_memory_fact_structurally(&partial));
        assert!(resources.satisfies_memory_fact_structurally(&partial));
        let restored = removed.unchecked_with_fact(owner);
        assert!(restored.satisfies_memory_fact_structurally(&partial));

        let slot = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(base.clone(), 0u32.into(), 1u32.into())),
        );
        assert!(slot.permits_memory_read(&base, 8, &empty));
        assert!(!slot.permits_memory_read(&base, 9, &empty));
        let alias = Pointer::symbolic(Variable(873_001));
        let equal = empty.assume_condition(ConditionTerm::pointer_equal(base, alias.clone()), true);
        assert!(equal.pointers_known_equal(&alias, &Pointer::symbolic(Variable(873_000)),));
        assert!(slot.permits_memory_read(&alias, 4, &equal));
        assert!(
            !slot.satisfies_memory_fact_structurally(&ResourceFact::view_memory(MemoryRange::new(
                alias,
                0u32.into(),
                1u32.into()
            ),))
        );
    }
}

#[cfg(test)]
#[test]
fn retained_plain_origin_requires_an_exact_allowed_atom() {
    use crate::kernel::{
        KernelTerm, KernelTermExport, MachineBinaryOp, MachineIntegerType as T,
        MachineOperandView as V,
    };
    let _session = crate::kernel::VerificationSession::enter();
    for (ty, term, expected) in [
        (T::Int32, MachineTerm::Variable(Variable(994530)), true),
        (T::Int32, MachineTerm::constant(3), true),
        (T::UInt32, MachineTerm::uint32_constant(3), true),
        (T::Int64, MachineTerm::int64_constant(3), true),
        (T::UInt64, MachineTerm::uint64_constant(3), false),
        (
            T::Int32,
            MachineTerm::Binary {
                format: T::Int32,
                op: MachineBinaryOp::Add,
                left: Box::new(MachineTerm::constant(1)),
                right: Box::new(MachineTerm::constant(2)),
            },
            false,
        ),
    ] {
        let root = KernelTerm::retained_machine_operand(ty, V::Legacy(&term));
        let offset = PointerOffsetTerm::Int32Scaled {
            value: V::Shared(&root).retain(T::Int32),
            byte_width: 4,
        };
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(plain_origin(&offset), expected, "{ty:?} {term:?}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
