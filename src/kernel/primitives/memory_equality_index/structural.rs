//! Structural resource candidates, maintained with the resource input.
//! This derived index is part of the trusted kernel. Hashes and geometric
//! matches select occurrences; the existing judgments check every occurrence.
use super::super::resource_algebra::{insert_resource_index_entry, remove_resource_index_entry};
use super::*;

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
// constant displacement. Symbolic indexing and snapshot matching need the
// shape payload instead; their membership is a checked judgment, not an
// ordering of affine vectors.
fn plain_origin(mut offset: &PointerOffsetTerm) -> bool {
    loop {
        match offset {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => return true,
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => {
                return matches!(
                    value.as_ref(),
                    Bitvector32Term::Variable(_)
                        | Bitvector32Term::Constant(_)
                        | Bitvector32Term::Int64Constant(_)
                );
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
            CResourceFact::own_memory(CMemoryRange::new(base.clone(), 0u32.into(), 4u32.into()));
        let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        let empty = PureFactContext::new();
        let partial = CResourceFact::view_memory(CMemoryRange::new(
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
            CResourceFact::own_memory(CMemoryRange::new(base.clone(), 0u32.into(), 1u32.into())),
        );
        assert!(slot.permits_memory_read(&base, 4, &empty));
        assert!(!slot.permits_memory_read(&base, 8, &empty));
        assert!(!slot.permits_memory_read(&base, 9, &empty));
        let pointer_slot = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                base.clone(),
                0u32.into(),
                1u32.into(),
                C_POINTER_BYTE_WIDTH,
            )),
        );
        assert!(pointer_slot.permits_memory_read(&base, C_POINTER_BYTE_WIDTH, &empty));
        assert!(!pointer_slot.permits_memory_read(&base, C_POINTER_BYTE_WIDTH + 1, &empty));
        let alias = Pointer::symbolic(Variable(873_001));
        let equal = empty.assume_condition(ConditionTerm::pointer_equal(base, alias.clone()), true);
        assert!(equal.pointers_known_equal(&alias, &Pointer::symbolic(Variable(873_000)),));
        assert!(slot.permits_memory_read(&alias, 4, &equal));
        assert!(
            !slot.satisfies_memory_fact_structurally(&CResourceFact::view_memory(
                CMemoryRange::new(alias, 0u32.into(), 1u32.into()),
            ))
        );
    }
}
