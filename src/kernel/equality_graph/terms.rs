//! Typed term classes inside the trusted graph: offset addition congruence and
//! int32 addition and registered same-snapshot int32 loads, connected by int32
//! scaling. Unsigned division/remainder and bitwise XOR have congruence only;
//! UInt64 arithmetic/bitwise applications, pointer addresses and complete
//! same-snapshot 64-bit reads share those classes. Other scalar operations
//! stay opaque; congruence supplies no arithmetic definedness.
//! Application signatures use operand classes; parent-use indexes propagate late
//! merges. Equal addresses in one block also equate their byte offsets.
//! No scalar arithmetic solving, cancellation, or general injectivity runs here.
//! Shallow keys preserve widths, signedness, and machine-term snapshot identity.

use super::{AffineOffset, MachineAtom, Pointer, PointerBlock, PointerOffsetTerm, Variable};
use crate::persistent::{PersistentMap, PersistentSet};
use std::sync::Arc;

mod congruence;

/// These tags keep signed division and wider integer operations distinct.
/// Congruence does not establish C/Rust arithmetic definedness.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Int32Binary {
    UnsignedDivide,
    UnsignedRemainder,
    BitwiseXor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum UInt64Binary {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    And,
    Or,
    Xor,
}

pub(super) fn uint64_binary(
    term: &crate::kernel::Bitvector32Term,
) -> Option<(
    UInt64Binary,
    &crate::kernel::Bitvector32Term,
    &crate::kernel::Bitvector32Term,
)> {
    use crate::kernel::Bitvector32Term as T;
    let (op, a, b) = match term {
        T::UInt64Add(a, b) => (UInt64Binary::Add, a, b),
        T::UInt64Subtract(a, b) => (UInt64Binary::Subtract, a, b),
        T::UInt64Multiply(a, b) => (UInt64Binary::Multiply, a, b),
        T::UInt64Divide(a, b) => (UInt64Binary::Divide, a, b),
        T::UInt64Remainder(a, b) => (UInt64Binary::Remainder, a, b),
        T::UInt64BitwiseAnd(a, b) => (UInt64Binary::And, a, b),
        T::UInt64BitwiseOr(a, b) => (UInt64Binary::Or, a, b),
        T::UInt64BitwiseXor(a, b) => (UInt64Binary::Xor, a, b),
        _ => return None,
    };
    Some((op, a, b))
}

pub(super) fn uint64_read(
    term: &crate::kernel::Bitvector32Term,
) -> Option<(crate::kernel::SharedCMemory, Pointer)> {
    use crate::kernel::{Bitvector32Term as T, LoadKind};
    match term {
        T::MemoryLoad(memory, pointer, LoadKind::Bits64) => {
            Some((memory.clone(), pointer.as_ref().clone()))
        }
        T::Variable(variable)
            if crate::kernel::registered_load_kind_for_variable(variable)
                == Some(LoadKind::Bits64)
                && crate::kernel::registered_load_bytes_for_variable(variable) == Some(8) =>
        {
            crate::kernel::registered_load_for_variable(variable)
        }
        _ => None,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Apply(u64, u64),
    Function(crate::kernel::SharedPureApplication, bool, usize),
    ArgumentTag(congruence::ArgumentTag),
    OpaqueArgument(crate::kernel::SharedPureApplication),
    Condition(congruence::ConditionKind, u64, u64),
    UInt64(MachineAtom),
    UInt64Binary(UInt64Binary, u64, u64),
    UInt64Address(u64),
    UInt64Read((u32, u32), u64),
    Address(u64, u64),
    AddressShift(u64, i64),
    PointerRead((u32, u32), u64, crate::kernel::LoadKind),
    Footprint(u64, u64),
    Int32(MachineAtom),
    Int32Add(u64, u64),
    Int32Binary(Int32Binary, u64, u64),
    Constant(i64),
    Variable(Variable),
    Add(u64, u64),
    Int32Scaled(u64, i64),
    Int64Scaled(MachineAtom, i64, bool),
}

// Operand IDs in an application are structural; in a signature they are
// current class roots. Constructor and width remain part of every signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Application {
    Apply(u64, u64),
    Condition(congruence::ConditionKind, u64, u64),
    UInt64Binary(UInt64Binary, u64, u64),
    UInt64Address(u64),
    UInt64Read((u32, u32), u64),
    Address(u64, u64),
    AddressShift(u64, i64),
    PointerRead((u32, u32), u64, crate::kernel::LoadKind),
    Footprint(u64, u64),
    Add(u64, u64),
    Int32Add(u64, u64),
    Int32Binary(Int32Binary, u64, u64),
    Int32Scaled(u64, i64),
    // Defining snapshot, exact storage block ID, offset node/class ID.
    // Only registered four-byte loads in the int32 interpretation enter here.
    Int32Load((u32, u32), u64, u64),
}

impl Application {
    fn operands(self) -> impl Iterator<Item = u64> {
        match self {
            Self::Apply(left, right)
            | Self::Condition(_, left, right)
            | Self::Add(left, right)
            | Self::UInt64Binary(_, left, right)
            | Self::Int32Add(left, right)
            | Self::Int32Binary(_, left, right)
            | Self::Footprint(left, right) => [Some(left), Some(right)],
            Self::Address(_, value)
            | Self::UInt64Address(value)
            | Self::UInt64Read(_, value)
            | Self::PointerRead(_, value, _)
            | Self::AddressShift(value, _)
            | Self::Int32Scaled(value, _)
            | Self::Int32Load(_, _, value) => [Some(value), None],
        }
        .into_iter()
        .flatten()
    }

    fn signature(self, classes: &TermClasses) -> Self {
        match self {
            Self::Apply(left, right) => Self::Apply(classes.root(left), classes.root(right)),
            Self::Condition(kind, left, right) => {
                Self::Condition(kind, classes.root(left), classes.root(right))
            }
            Self::UInt64Binary(op, left, right) => {
                Self::UInt64Binary(op, classes.root(left), classes.root(right))
            }
            Self::UInt64Address(address) => Self::UInt64Address(classes.root(address)),
            Self::UInt64Read(snapshot, address) => {
                Self::UInt64Read(snapshot, classes.root(address))
            }
            Self::Address(block, offset) => Self::Address(block, classes.root(offset)),
            Self::AddressShift(address, bytes) => Self::AddressShift(classes.root(address), bytes),
            Self::PointerRead(snapshot, address, kind) => {
                Self::PointerRead(snapshot, classes.root(address), kind)
            }
            Self::Footprint(start, end) => Self::Footprint(classes.root(start), classes.root(end)),
            Self::Add(left, right) => Self::Add(classes.root(left), classes.root(right)),
            Self::Int32Add(left, right) => Self::Int32Add(classes.root(left), classes.root(right)),
            Self::Int32Binary(op, left, right) => {
                Self::Int32Binary(op, classes.root(left), classes.root(right))
            }
            Self::Int32Scaled(value, width) => Self::Int32Scaled(classes.root(value), width),
            Self::Int32Load(snapshot, block, offset) => {
                Self::Int32Load(snapshot, block, classes.root(offset))
            }
        }
    }
}

#[derive(Clone, Copy)]
pub(in crate::kernel) struct TermClassMerge {
    pub(in crate::kernel) moved: u64,
    pub(in crate::kernel) kept: u64,
}
#[derive(Clone)]
struct MergeHistory {
    depth: usize,
    merge: TermClassMerge,
    parent: Option<Arc<MergeHistory>>,
}

// This is disposable derived state, not proof-context storage. Forking starts
// an empty local cache in constant work instead of copying a growing table.
#[derive(Default)]
struct RootLookupCache(std::cell::RefCell<std::collections::HashMap<u64, (usize, u64)>>);

impl Clone for RootLookupCache {
    fn clone(&self) -> Self {
        Self::default()
    }
}

#[derive(Clone, Default)]
pub(super) struct TermClasses {
    condition_kinds: PersistentSet<(congruence::ConditionKind, bool)>,
    // Truth is an annotation of a condition class, not a union between all
    // true facts. Unrelated order facts must not create value equivalences.
    condition_truth: PersistentMap<u64, u8>,
    // Constant signed int32 bounds belong to a value class, not a spelling.
    // A class union intersects two intervals in constant local work.
    signed_int32_intervals: PersistentMap<u64, (i64, i64)>,
    origin: Arc<()>,
    // Completeness metadata for affine interval consumers, not equality facts.
    // Propagates once per affected class/application through indexed uses.
    non_affine_classes: PersistentSet<u64>,
    affine_applications: PersistentMap<u64, PersistentSet<u64>>,
    affine_uses: PersistentMap<u64, PersistentSet<u64>>,
    // Only applications with literal-folding rules need revisiting when an
    // existing class first learns a constant. Boolean observations do not.
    constant_uses: PersistentMap<u64, PersistentSet<u64>>,
    non_affine_address_blocks: PersistentSet<PointerBlock>,
    address_blocks: PersistentMap<u64, PointerBlock>,
    history: Option<Arc<MergeHistory>>,
    // Node IDs are local to a persistent registration prefix. The last marker
    // detects divergent query registrations without scanning that prefix.
    markers: PersistentMap<u64, Arc<()>>,
    address_uses: PersistentMap<PointerBlock, PersistentMap<u64, Arc<PointerOffsetTerm>>>,
    address_nodes: PersistentSet<u64>,
    // A displacement definition is permanent for one raw address spelling.
    // Repeated queries reuse it without re-registering its base or closure.
    registered_address_shifts: PersistentSet<(u64, u64)>,
    // The address node of each registered (block, raw offset) spelling. Its
    // affine definition is permanent, so a repeated registration (every
    // pointer equality query registers both sides) returns it after interning
    // the offset, without renormalizing or reclosing. Keys are shallow IDs.
    registered_addresses: PersistentMap<(u64, u64), u64>,
    // One offset witness per exact block in each address class. When address
    // classes merge, a shared block proves its two offsets equal. Small-side
    // class union visits only moved witnesses, never ambient pointer facts.
    offsets_by_address_block: PersistentMap<u64, PersistentMap<u64, u64>>,
    // Retained concrete address evidence follows typed class merges. This
    // disambiguates parameters sharing the external address-space block.
    storage_addresses: PersistentMap<u64, Option<Pointer>>,
    // One producer-registered additive spelling per index width and address
    // class. A narrow spelling must not discard the wide coordinate whose
    // bounds justify a borrow. Queries never enumerate class members.
    additive_addresses: PersistentMap<u64, (Option<Arc<Pointer>>, Option<Arc<Pointer>>)>,
    // Same-block pointer comparisons enter as offset equalities. Their checked
    // producer spellings carry no block identity and are applied only in the
    // query's own block.
    additive_offsets: PersistentMap<
        u64,
        (
            Option<Arc<PointerOffsetTerm>>,
            Option<Arc<PointerOffsetTerm>>,
        ),
    >,
    alignment_witnesses: PersistentMap<u64, (u64, Pointer)>,
    // One zero-offset typed-read value per class. Congruence emits only
    // newly identified pairs for the legacy affine/index projection.
    read_witnesses: PersistentMap<u64, PointerBlock>,
    read_merges: imbl::Vector<(PointerBlock, PointerBlock)>,
    nodes: PersistentMap<Node, u64>,
    load_blocks: PersistentMap<PointerBlock, u64>,
    registered_int32_loads: PersistentSet<u64>,
    // Registration dependencies are drained before any public answer. Keeping
    // this worklist iterative handles loads used as indices of further loads.
    pending_loads: Vec<(u64, crate::kernel::SharedCMemory, crate::kernel::Pointer)>,
    // Weight counts class members plus registered parent uses. Moving the
    // lighter side bounds both root depth and reindexing, including a class
    // with many application parents repeatedly joined to fresh singleton terms.
    parents: PersistentMap<u64, u64>,
    // Cache representative lookups under the current merge epoch. A new union
    // invalidates entries lazily, without a scan. Keys are shallow node IDs,
    // with at most one entry per node; semantic graph roots remain persistent.
    root_cache: RootLookupCache,
    weights: PersistentMap<u64, usize>,
    int32_constants: PersistentMap<u64, i32>,
    applications: PersistentMap<u64, Application>,
    uses: PersistentMap<u64, PersistentSet<u64>>,
    signatures: PersistentMap<Application, u64>,
    application_signatures: PersistentMap<u64, Application>,
}

impl TermClasses {
    pub(super) fn merges_since(&self, ancestor: &Self) -> Option<Vec<TermClassMerge>> {
        if !Arc::ptr_eq(&self.origin, &ancestor.origin) {
            return None;
        }
        if let Some(last) = ancestor.nodes.len().checked_sub(1) {
            let marker = self.markers.get(&(last as u64))?;
            if !Arc::ptr_eq(marker, ancestor.markers.get(&(last as u64))?) {
                return None;
            }
        }
        let mut cursor = self.history.clone();
        let previous = &ancestor.history;
        let previous_depth = previous.as_ref().map_or(0, |node| node.depth);
        let mut merges = Vec::new();
        while !match (&cursor, previous) {
            (None, None) => true,
            (Some(current), Some(previous)) => Arc::ptr_eq(current, previous),
            _ => false,
        } {
            let node = cursor.as_ref()?;
            if node.depth <= previous_depth {
                return None;
            }
            crate::instrumentation::record_deterministic_work(1);
            merges.push(node.merge);
            cursor = node.parent.clone();
        }
        merges.reverse();
        Some(merges)
    }

    pub(super) fn address(
        &mut self,
        block: PointerBlock,
        offset: PointerOffsetTerm,
    ) -> (u64, bool) {
        let (address, new, raw_offset) = self.address_without_shift(block.clone(), offset.clone());
        // Preserve the byte displacement as an operation on the complete
        // address. Flattening it into a block's affine coordinates can hide
        // the aliased base subexpression after a previous block merge.
        // One selected prefix suffices; do not recursively publish prefixes
        // or enumerate other addresses in the class.
        let shift = match &offset {
            PointerOffsetTerm::Add(base, displacement) => displacement
                .as_const()
                .filter(|bytes| *bytes != 0)
                .map(|bytes| (base.as_ref().clone(), bytes)),
            PointerOffsetTerm::Constant(bytes) if *bytes != 0 => {
                Some((PointerOffsetTerm::Constant(0), *bytes))
            }
            _ => None,
        };
        if let Some((base, bytes)) = shift
            && !self
                .registered_address_shifts
                .contains(&(address, raw_offset))
        {
            let base = self.address_without_shift(block, base).0;
            let shifted = self.intern_node(Node::AddressShift(base, bytes));
            self.close_with_affine_definition(vec![(address, shifted)], true);
            self.registered_address_shifts = self
                .registered_address_shifts
                .with_value((address, raw_offset));
        }
        (address, new)
    }

    /// A typed pointer read is an application of the complete address, not
    /// its affine block representative. Existing parent uses propagate late
    /// address merges without enumerating aliases or unrelated reads.
    pub(super) fn pointer_read(
        &mut self,
        snapshot: (u32, u32),
        address: u64,
        kind: crate::kernel::LoadKind,
        value: u64,
        block: PointerBlock,
    ) {
        let read = self.intern_node(Node::PointerRead(snapshot, address, kind));
        self.close_with_affine_definition(vec![(value, read)], true);
        self.retain_read_witness(self.root(value), block);
    }

    fn retain_read_witness(&mut self, root: u64, block: PointerBlock) {
        if let Some(other) = self.read_witnesses.get(&root) {
            if other != &block {
                self.read_merges.push_back((other.clone(), block));
            }
        } else {
            self.read_witnesses.insert(root, block);
        }
    }

    pub(super) fn take_read_merges(&mut self) -> imbl::Vector<(PointerBlock, PointerBlock)> {
        std::mem::take(&mut self.read_merges)
    }

    #[cfg(test)]
    pub(super) fn node_count(&self) -> usize {
        self.nodes.len()
    }

    fn address_without_shift(
        &mut self,
        block: PointerBlock,
        offset: PointerOffsetTerm,
    ) -> (u64, bool, u64) {
        // Affine normalization is already trusted by pointer equality. Keep
        // the original syntax connected to its definitional normal form so
        // whole-offset premises and affine addresses share these applications.
        let raw = self.intern(&offset);
        if let Some(block_id) = self.load_blocks.get(&block)
            && let Some(id) = self.registered_addresses.get(&(*block_id, raw)).copied()
        {
            self.register_pending_loads();
            return (id, false, raw);
        }
        let normalized = AffineOffset::of(&offset).and_then(|value| value.to_offset_term());
        let operand = normalized.as_ref().map_or(raw, |term| self.intern(term));
        self.register_pending_loads();
        self.close_with_affine_definition(vec![(raw, operand)], true);
        let next_block = self.load_blocks.len() as u64;
        let block_id = match self.load_blocks.get(&block) {
            Some(id) => *id,
            None => {
                self.address_blocks.insert(next_block, block.clone());
                self.load_blocks.insert(block.clone(), next_block);
                next_block
            }
        };
        let node = Node::Address(block_id, operand);
        let new = !self.nodes.contains_key(&node);
        let id = self.intern_node(node);
        self.registered_addresses.insert((block_id, raw), id);
        let mut uses = self.address_uses.get(&block).cloned().unwrap_or_default();
        if !uses.contains_key(&id) {
            uses.insert(id, Arc::new(offset));
            self.address_uses.insert(block, uses);
        }
        (id, new, raw)
    }

    /// Only original concrete address inputs carry storage evidence. Affine
    /// projections into a representative's coordinates must never mint it.
    pub(super) fn retain_storage_address(&mut self, id: u64, storage: &Pointer) {
        let root = self.root(id);
        let retained = match self.storage_addresses.get(&root) {
            None => Some(storage.clone()),
            Some(Some(previous)) if previous.block == storage.block => Some(previous.clone()),
            _ => None,
        };
        self.storage_addresses.insert(root, retained);
    }

    pub(super) fn storage_address(&self, id: u64) -> Option<Pointer> {
        self.storage_addresses
            .get(&self.root(id))
            .cloned()
            .flatten()
    }

    fn merge_address_offsets(&mut self, moved: u64, kept: u64, pending: &mut Vec<(u64, u64)>) {
        let Some(moved_offsets) = self.offsets_by_address_block.get(&moved).cloned() else {
            return;
        };
        let mut kept_offsets = self
            .offsets_by_address_block
            .get(&kept)
            .cloned()
            .unwrap_or_default();
        for (block, offset) in moved_offsets.iter() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(previous) = kept_offsets.get(block) {
                pending.push((*previous, *offset));
            } else {
                kept_offsets.insert(*block, *offset);
            }
        }
        self.offsets_by_address_block.remove(&moved);
        self.offsets_by_address_block.insert(kept, kept_offsets);
    }

    fn merge_storage_addresses(&mut self, moved: u64, kept: u64) {
        let merged = match (
            self.storage_addresses.get(&moved).cloned(),
            self.storage_addresses.get(&kept).cloned(),
        ) {
            (None, right) => right,
            (left, None) => left,
            (Some(Some(left)), Some(Some(right))) if left.block == right.block => Some(Some(right)),
            _ => Some(None),
        };
        if let Some(merged) = merged {
            self.storage_addresses.insert(kept, merged);
        }
        self.storage_addresses.remove(&moved);
    }

    pub(super) fn retain_additive_address(&mut self, id: u64, pointer: &Pointer) {
        if !matches!(pointer.offset, PointerOffsetTerm::Add(_, _)) {
            return;
        }
        let wide = Self::additive_offset_is_wide(&pointer.offset);
        let root = self.root(id);
        let mut spellings = self
            .additive_addresses
            .get(&root)
            .cloned()
            .unwrap_or_default();
        let selected = if wide {
            &mut spellings.1
        } else {
            &mut spellings.0
        };
        if selected
            .as_ref()
            .is_none_or(|prior| wide && Self::prefer_wide_offset(&pointer.offset, &prior.offset))
        {
            *selected = Some(Arc::new(pointer.clone()));
            self.additive_addresses.insert(root, spellings);
        }
    }

    // A wide supplier checks the final displacement in its uint64 coordinate.
    // Prefer that producer over a wide prefix followed by a signed displacement;
    // both denote the same checked address, but only the former retains the
    // native index on which the caller stated its window bounds.
    fn prefer_wide_offset(new: &PointerOffsetTerm, prior: &PointerOffsetTerm) -> bool {
        let native = |offset: &PointerOffsetTerm| {
            matches!(offset,
            PointerOffsetTerm::Add(_, right) if matches!(right.as_ref(),
                PointerOffsetTerm::Int64Scaled { unsigned: true, .. }))
        };
        native(new) && !native(prior)
    }

    fn additive_offset_is_wide(offset: &PointerOffsetTerm) -> bool {
        let mut pending = vec![offset];
        let mut wide = false;
        while let Some(offset) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match offset {
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                PointerOffsetTerm::Int64Scaled { .. } => {
                    wide = true;
                    break;
                }
                _ => {}
            }
        }
        wide
    }

    fn retain_additive_offset(&mut self, id: u64, offset: &PointerOffsetTerm) {
        if !matches!(offset, PointerOffsetTerm::Add(_, _)) {
            return;
        }
        let wide = Self::additive_offset_is_wide(offset);
        let root = self.root(id);
        let mut spellings = self
            .additive_offsets
            .get(&root)
            .cloned()
            .unwrap_or_default();
        let selected = if wide {
            &mut spellings.1
        } else {
            &mut spellings.0
        };
        if selected
            .as_ref()
            .is_none_or(|prior| wide && Self::prefer_wide_offset(offset, prior))
        {
            *selected = Some(Arc::new(offset.clone()));
            self.additive_offsets.insert(root, spellings);
        }
    }

    pub(super) fn additive_offset(
        &mut self,
        offset: &PointerOffsetTerm,
        wide: bool,
    ) -> Option<PointerOffsetTerm> {
        let id = self.intern(offset);
        let (narrow, wide_spelling) = self.additive_offsets.get(&self.root(id))?;
        (if wide {
            wide_spelling.as_ref()
        } else {
            narrow.as_ref().or(wide_spelling.as_ref())
        })
        .map(|offset| (**offset).clone())
    }

    fn merge_additive_offsets(&mut self, moved: u64, kept: u64) {
        if let Some((narrow, wide)) = self.additive_offsets.get(&moved).cloned() {
            let mut spellings = self
                .additive_offsets
                .get(&kept)
                .cloned()
                .unwrap_or_default();
            if spellings.0.is_none() {
                spellings.0 = narrow;
            }
            if let Some(wide) = wide
                && spellings
                    .1
                    .as_ref()
                    .is_none_or(|prior| Self::prefer_wide_offset(&wide, prior))
            {
                spellings.1 = Some(wide);
            }
            self.additive_offsets.insert(kept, spellings);
        }
        self.additive_offsets.remove(&moved);
    }

    pub(super) fn additive_address(&self, id: u64) -> Option<Pointer> {
        self.additive_addresses
            .get(&self.root(id))
            .and_then(|(narrow, wide)| narrow.as_ref().or(wide.as_ref()))
            .map(|pointer| (**pointer).clone())
    }

    pub(super) fn wide_additive_address(&self, id: u64) -> Option<Pointer> {
        self.additive_addresses
            .get(&self.root(id))
            .and_then(|(_, wide)| wide.as_ref())
            .map(|pointer| (**pointer).clone())
    }

    fn merge_additive_addresses(&mut self, moved: u64, kept: u64) {
        if let Some((narrow, wide)) = self.additive_addresses.get(&moved).cloned() {
            let mut spellings = self
                .additive_addresses
                .get(&kept)
                .cloned()
                .unwrap_or_default();
            if spellings.0.is_none() {
                spellings.0 = narrow;
            }
            if let Some(wide) = wide
                && spellings
                    .1
                    .as_ref()
                    .is_none_or(|prior| Self::prefer_wide_offset(&wide.offset, &prior.offset))
            {
                spellings.1 = Some(wide);
            }
            self.additive_addresses.insert(kept, spellings);
        }
        self.additive_addresses.remove(&moved);
    }

    pub(super) fn retain_alignment(&mut self, id: u64, alignment: u64, pointer: &Pointer) {
        let root = self.root(id);
        if self
            .alignment_witnesses
            .get(&root)
            .is_none_or(|(old, _)| *old < alignment)
        {
            self.alignment_witnesses
                .insert(root, (alignment, pointer.clone()));
        }
    }

    pub(super) fn alignment_witness(&self, id: u64) -> Option<(u64, Pointer)> {
        self.alignment_witnesses.get(&self.root(id)).cloned()
    }

    fn merge_alignment_witnesses(&mut self, moved: u64, kept: u64) {
        if let Some((alignment, pointer)) = self.alignment_witnesses.get(&moved).cloned() {
            self.retain_alignment(kept, alignment, &pointer);
        }
        self.alignment_witnesses.remove(&moved);
    }

    pub(super) fn footprint(&mut self, start: u64, end: u64) -> u64 {
        let id = self.intern_node(Node::Footprint(start, end));
        self.root(id)
    }

    pub(super) fn shift_addresses(
        &mut self,
        moved: &PointerBlock,
        kept: &PointerBlock,
        delta: &AffineOffset,
    ) {
        if !self.affine_addresses_complete(moved) {
            self.non_affine_address_blocks =
                self.non_affine_address_blocks.with_value(kept.clone());
        }
        let Some(uses) = self.address_uses.get(moved).cloned() else {
            return;
        };
        let Some(delta) = delta.to_offset_term() else {
            // The affine block relation remains valid, but its displacement
            // has no bounded spelling in this term fragment. Do not let a
            // consumer turn incomplete address registrations into a denial.
            return;
        };
        self.address_uses.remove(moved);
        for (id, offset) in uses.iter() {
            crate::instrumentation::record_deterministic_work(1);
            let translated =
                PointerOffsetTerm::Add(Box::new((**offset).clone()), Box::new(delta.clone()));
            let (new, _) = self.address(kept.clone(), translated);
            self.close(vec![(*id, new)]);
        }
    }

    /// Checked pointer premises join address applications in the same closure
    /// that propagates whole-offset equality. No adjacency search is retained.
    pub(super) fn add_address_equality(&mut self, left: u64, right: u64) -> bool {
        debug_assert!(self.address_nodes.contains(&left));
        debug_assert!(self.address_nodes.contains(&right));
        self.close(vec![(left, right)])
    }

    pub(super) fn class_root(&self, id: u64) -> u64 {
        self.root(id)
    }

    pub(super) fn has_equivalences(&self) -> bool {
        !self.parents.is_empty()
    }

    /// A non-affine offset equality can add suppliers not represented by an
    /// affine interval tree. Report unknown only for address blocks reached by
    /// that equality's registered parent dependencies. No class/frame walk.
    pub(super) fn affine_addresses_complete(&self, block: &PointerBlock) -> bool {
        !self.non_affine_address_blocks.contains(block)
    }

    fn mark_non_affine(&mut self, id: u64) {
        let mut pending = vec![id];
        while let Some(id) = pending.pop() {
            let root = self.root(id);
            if self.non_affine_classes.contains(&root) {
                continue;
            }
            crate::instrumentation::record_deterministic_work(1);
            self.non_affine_classes = self.non_affine_classes.with_value(root);
            let applications = self
                .affine_applications
                .get(&root)
                .cloned()
                .unwrap_or_default();
            self.affine_applications.remove(&root);
            for id in applications.iter() {
                crate::instrumentation::record_deterministic_work(1);
                let application = *self.applications.get(id).expect("application");
                if let Application::Address(block, _) = application {
                    let block = self.address_blocks.get(&block).expect("address block");
                    self.non_affine_address_blocks =
                        self.non_affine_address_blocks.with_value(block.clone());
                }
                // Remove already-affected parents from the completeness-use
                // index. A later fork must not revisit them just because one
                // previously unrelated operand learns its first alias.
                for operand in application.operands() {
                    let operand = self.root(operand);
                    if let Some(uses) = self.affine_uses.get(&operand) {
                        let uses = uses.without_value(id);
                        if uses.is_empty() {
                            self.affine_uses.remove(&operand);
                        } else {
                            self.affine_uses.insert(operand, uses);
                        }
                    }
                }
            }
            if let Some(uses) = self.affine_uses.get(&root) {
                pending.extend(uses.iter().copied());
            }
        }
    }

    fn merge_affine_applications(&mut self, moved: u64, kept: u64) {
        // Only clean classes retain these sets. Each moved application/use is
        // already charged to the graph's smaller-side union weight.
        for map in [&mut self.affine_applications, &mut self.affine_uses] {
            if let Some(moved_set) = map.get(&moved).cloned() {
                let mut kept_set = map.get(&kept).cloned().unwrap_or_default();
                for id in moved_set.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    kept_set = kept_set.with_value(*id);
                }
                map.remove(&moved);
                map.insert(kept, kept_set);
            }
        }
    }

    fn intern(&mut self, term: &PointerOffsetTerm) -> u64 {
        enum Work<'a> {
            Term(&'a PointerOffsetTerm),
            Add,
        }
        let mut pending = vec![Work::Term(term)];
        let mut values = Vec::new();
        while let Some(work) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let node = match work {
                Work::Add => {
                    let right = values.pop().expect("right offset");
                    let left = values.pop().expect("left offset");
                    Node::Add(left, right)
                }
                Work::Term(term) => match term {
                    PointerOffsetTerm::Constant(value) => Node::Constant(*value),
                    PointerOffsetTerm::Variable(variable) => Node::Variable(*variable),
                    PointerOffsetTerm::Add(left, right) => {
                        pending.push(Work::Add);
                        pending.push(Work::Term(right));
                        pending.push(Work::Term(left));
                        continue;
                    }
                    PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                        Node::Int32Scaled(self.intern_int32(value), *byte_width)
                    }
                    PointerOffsetTerm::Int64Scaled {
                        value,
                        byte_width,
                        unsigned,
                    } => Node::Int64Scaled(
                        MachineAtom::new(
                            if *unsigned {
                                crate::kernel::MachineIntegerType::UInt64
                            } else {
                                crate::kernel::MachineIntegerType::Int64
                            },
                            crate::kernel::canonical_term(value),
                        ),
                        *byte_width,
                        *unsigned,
                    ),
                },
            };
            let id = self.intern_node(node);
            values.push(id);
        }
        values.pop().expect("offset term")
    }

    fn intern_node(&mut self, node: Node) -> u64 {
        if let Some(id) = self.nodes.get(&node).copied() {
            self.enqueue_int32_load(id, &node);
            return id;
        }
        let id = self.nodes.len() as u64;
        let application = match &node {
            Node::Apply(left, right) => Some(Application::Apply(*left, *right)),
            Node::Condition(kind, left, right) => {
                Some(Application::Condition(*kind, *left, *right))
            }
            Node::UInt64Binary(op, left, right) => {
                Some(Application::UInt64Binary(*op, *left, *right))
            }
            Node::UInt64Address(address) => Some(Application::UInt64Address(*address)),
            Node::UInt64Read(snapshot, address) => {
                Some(Application::UInt64Read(*snapshot, *address))
            }
            Node::Address(block, offset) => {
                self.address_nodes = self.address_nodes.with_value(id);
                self.offsets_by_address_block
                    .insert(id, PersistentMap::default().with_inserted(*block, *offset));
                Some(Application::Address(*block, *offset))
            }
            Node::AddressShift(address, bytes) => {
                self.address_nodes = self.address_nodes.with_value(id);
                Some(Application::AddressShift(*address, *bytes))
            }
            Node::PointerRead(snapshot, address, kind) => {
                Some(Application::PointerRead(*snapshot, *address, *kind))
            }
            Node::Footprint(start, end) => Some(Application::Footprint(*start, *end)),
            Node::Add(left, right) => Some(Application::Add(*left, *right)),
            Node::Int32Add(left, right) => Some(Application::Int32Add(*left, *right)),
            Node::Int32Binary(op, left, right) => {
                Some(Application::Int32Binary(*op, *left, *right))
            }
            Node::Int32Scaled(value, width) => Some(Application::Int32Scaled(*value, *width)),
            Node::Int32(value) => {
                if let Some(value) = value.value().as_const() {
                    self.int32_constants.insert(id, value as i32);
                }
                None
            }
            _ => None,
        };
        self.enqueue_int32_load(id, &node);
        self.nodes.insert(node, id);
        self.markers.insert(id, Arc::new(()));
        if let Some(application) = application {
            self.register_application(id, application);
        }
        id
    }

    fn enqueue_int32_load(&mut self, id: u64, node: &Node) {
        let Node::Int32(atom) = node else { return };
        let crate::kernel::Bitvector32Term::Variable(variable) = atom.value() else {
            return;
        };
        // Only a four-byte integer read is an int32 load application: a
        // narrower read named at an address a wider read was recorded at
        // carries that wider width, and is still another value.
        if !crate::kernel::is_load_variable(variable)
            || self.registered_int32_loads.contains(&id)
            || crate::kernel::registered_load_bytes_for_variable(variable) != Some(4)
            || crate::kernel::registered_load_kind_for_variable(variable)
                != Some(crate::kernel::LoadKind::Bits32)
        {
            return;
        }
        let Some((memory, pointer)) = crate::kernel::registered_load_for_variable(variable) else {
            return;
        };
        // This is the registered defining snapshot, not the mutable live
        // origin. Canonicalization already justified any projection; this
        // graph neither walks history nor equates distinct snapshot IDs.
        self.registered_int32_loads = self.registered_int32_loads.with_value(id);
        self.pending_loads.push((id, memory, pointer));
    }

    fn register_pending_loads(&mut self) {
        while let Some((id, memory, pointer)) = self.pending_loads.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let next_block = self.load_blocks.len() as u64;
            let block = match self.load_blocks.get(&pointer.block) {
                Some(block) => *block,
                None => {
                    self.address_blocks
                        .insert(next_block, pointer.block.clone());
                    self.load_blocks.insert(pointer.block, next_block);
                    next_block
                }
            };
            let offset = self.intern(&pointer.offset);
            self.register_application(
                id,
                Application::Int32Load(memory.read_identity(), block, offset),
            );
        }
    }

    fn intern_uint64(&mut self, term: &crate::kernel::Bitvector32Term) -> u64 {
        self.intern_machine(term, true)
    }

    pub(super) fn are_uint64_equal(
        &mut self,
        left: &crate::kernel::Bitvector32Term,
        right: &crate::kernel::Bitvector32Term,
    ) -> bool {
        let left = self.intern_uint64(left);
        let right = self.intern_uint64(right);
        self.register_pending_loads();
        self.root(left) == self.root(right)
    }

    pub(super) fn add_uint64_equality(
        &mut self,
        left: &crate::kernel::Bitvector32Term,
        right: &crate::kernel::Bitvector32Term,
    ) -> bool {
        let left = self.intern_uint64(left);
        let right = self.intern_uint64(right);
        self.register_pending_loads();
        left != right && self.close(vec![(left, right)])
    }

    fn intern_int32(&mut self, term: &crate::kernel::Bitvector32Term) -> u64 {
        let term = crate::kernel::canonical_term(term);
        self.intern_machine(&term, false)
    }

    pub(super) fn int32_class(&mut self, term: &crate::kernel::Bitvector32Term) -> u64 {
        let node = self.intern_int32(term);
        self.register_pending_loads();
        self.root(node)
    }

    pub(super) fn signed_int32_interval(&self, node: u64) -> Option<(i64, i64)> {
        self.signed_int32_intervals
            .get(&self.root(node))
            .copied()
            .filter(|(lower, upper)| lower <= upper)
    }

    fn retain_signed_int32_interval(
        &mut self,
        term: &crate::kernel::Bitvector32Term,
        lower: i64,
        upper: i64,
    ) {
        let node = self.intern_int32(term);
        self.register_pending_loads();
        let root = self.root(node);
        let previous = self
            .signed_int32_intervals
            .get(&root)
            .copied()
            .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
        self.signed_int32_intervals
            .insert(root, (previous.0.max(lower), previous.1.min(upper)));
        crate::instrumentation::record_deterministic_work(1);
    }

    pub(super) fn are_int32_equal(
        &mut self,
        left: &crate::kernel::Bitvector32Term,
        right: &crate::kernel::Bitvector32Term,
    ) -> bool {
        use crate::kernel::Bitvector32Term;
        if left == right {
            return true;
        }
        // Opaque atoms cannot acquire equality by query registration. Consult
        // their existing nodes directly, avoiding registration of unrelated
        // order endpoints and unsupported expressions. Loads and addition
        // still need registration because their definitions can join classes.
        let opaque = |term: &Bitvector32Term| {
            let supported = |term: &Bitvector32Term| match term {
                Bitvector32Term::ClickFunctionApplication { .. }
                | Bitvector32Term::Add(..)
                | Bitvector32Term::MemoryLoad(..)
                | Bitvector32Term::UnsignedDivide(..)
                | Bitvector32Term::UnsignedRemainder(..)
                | Bitvector32Term::BitwiseXor(..) => true,
                Bitvector32Term::Variable(variable) => crate::kernel::is_load_variable(variable),
                _ => false,
            };
            if supported(term) {
                return None;
            }
            let term = crate::kernel::canonical_term(term);
            (!supported(&term)).then(|| Node::Int32(MachineAtom::int32(term)))
        };
        let left_atom = opaque(left);
        let right_atom = opaque(right);
        if left_atom.is_some() && left_atom == right_atom {
            return true;
        }
        // Registration can create a literal through evaluation, but cannot
        // create a new opaque nonliteral atom as another term's consequence.
        // Such an absent endpoint therefore cannot match an application.
        for atom in [&left_atom, &right_atom].into_iter().flatten() {
            if let Node::Int32(value) = atom
                && !matches!(value.value(), Bitvector32Term::Constant(_))
                && !self.nodes.contains_key(atom)
            {
                return false;
            }
        }
        if let (Some(left), Some(right)) = (left_atom, right_atom) {
            // Predicate signatures may register operands without equating any
            // values. Distinct opaque atoms cannot meet in that graph.
            if !self.has_equivalences() {
                return false;
            }
            return match (self.nodes.get(&left), self.nodes.get(&right)) {
                (Some(left), Some(right)) => {
                    left == right
                        || ((self.parents.contains_key(left) || self.parents.contains_key(right))
                            && self.root(*left) == self.root(*right))
                }
                _ => false,
            };
        }
        let left = self.intern_int32(left);
        let right = self.intern_int32(right);
        self.register_pending_loads();
        // Reflexivity needs no class traversal, even when this node was merged.
        left == right || self.root(left) == self.root(right)
    }

    pub(super) fn add_int32_equality(
        &mut self,
        left: &crate::kernel::Bitvector32Term,
        right: &crate::kernel::Bitvector32Term,
    ) -> bool {
        let left = self.intern_int32(left);
        let right = self.intern_int32(right);
        self.register_pending_loads();
        left != right && self.close(vec![(left, right)])
    }

    fn root(&self, mut id: u64) -> u64 {
        let original = id;
        let epoch = self.history.as_ref().map_or(0, |history| history.depth);
        if let Some((cached_epoch, root)) = self.root_cache.0.borrow().get(&id).copied()
            && cached_epoch == epoch
        {
            return root;
        }
        loop {
            crate::instrumentation::record_deterministic_work(1);
            match self.parents.get(&id) {
                Some(parent) => id = *parent,
                None => break,
            }
        }
        self.root_cache.0.borrow_mut().insert(original, (epoch, id));
        id
    }

    pub(super) fn are_equal(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        let left = self.intern(left);
        let right = self.intern(right);
        self.register_pending_loads();
        self.root(left) == self.root(right)
    }

    pub(super) fn add_equality(
        &mut self,
        left: &PointerOffsetTerm,
        right: &PointerOffsetTerm,
    ) -> bool {
        let left_id = self.intern(left);
        let right_id = self.intern(right);
        self.retain_additive_offset(left_id, left);
        self.retain_additive_offset(right_id, right);
        self.register_pending_loads();
        self.close(vec![(left_id, right_id)])
    }

    fn weight(&self, id: u64) -> usize {
        self.weights.get(&id).copied().unwrap_or(1)
    }

    fn register_application(&mut self, id: u64, application: Application) {
        self.applications.insert(id, application);
        let class = self.root(id);
        // Conditions and footprint predicates are boolean observations,
        // never address operands. Their congruence uses remain in `uses`.
        let affine = !matches!(
            application,
            Application::Condition(..) | Application::Footprint(..)
        ) && !self.non_affine_classes.contains(&class);
        if affine {
            let applications = self
                .affine_applications
                .get(&class)
                .cloned()
                .unwrap_or_default();
            self.affine_applications
                .insert(class, applications.with_value(id));
        }
        for operand in application.operands() {
            let root = self.root(operand);
            if matches!(
                application,
                Application::Int32Add(..) | Application::Int32Scaled(..)
            ) {
                let uses = self.constant_uses.get(&root).cloned().unwrap_or_default();
                self.constant_uses.insert(root, uses.with_value(id));
            }
            if affine {
                let uses = self.affine_uses.get(&root).cloned().unwrap_or_default();
                self.affine_uses.insert(root, uses.with_value(id));
            }
            let uses = self.uses.get(&root).cloned().unwrap_or_default();
            if !uses.contains(&id) {
                self.uses.insert(root, uses.with_value(id));
                self.weights.insert(root, self.weight(root) + 1);
            }
        }
        let mut pending = Vec::new();
        self.reindex_application(id, &mut pending);
        self.close(pending);
    }

    fn reindex_application(&mut self, id: u64, pending: &mut Vec<(u64, u64)>) {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(old) = self.application_signatures.get(&id).copied()
            && self.signatures.get(&old) == Some(&id)
        {
            self.signatures.remove(&old);
        }
        let signature = self
            .applications
            .get(&id)
            .expect("registered application")
            .signature(self);
        if signature
            .operands()
            .any(|operand| self.non_affine_classes.contains(&operand))
        {
            if let Application::Address(block, _) = signature {
                let block = self.address_blocks.get(&block).expect("address block");
                self.non_affine_address_blocks =
                    self.non_affine_address_blocks.with_value(block.clone());
            }
            self.mark_non_affine(id);
        }
        // PointerOffsetTerm folds literal int32 indices to byte constants.
        // Join that definitional form without solving any scalar arithmetic.
        if let Application::Int32Scaled(value, width) = signature
            && let Some(value) = self.int32_constants.get(&value)
            && let Some(bytes) = i64::from(*value).checked_mul(width)
        {
            let constant = self.intern_node(Node::Constant(bytes));
            pending.push((id, constant));
        }
        // Kernel int32 values are bitvectors. Folding their sum wraps at 32
        // bits, just like Bitvector32Term::as_const; C signed definedness is a
        // separate obligation and is not established by equality congruence.
        if let Application::Int32Add(left, right) = signature
            && let (Some(left), Some(right)) = (
                self.int32_constants.get(&left),
                self.int32_constants.get(&right),
            )
        {
            let value = left.wrapping_add(*right) as u32;
            let constant = self.intern_node(Node::Int32(MachineAtom::int32(
                crate::kernel::Bitvector32Term::Constant(value),
            )));
            pending.push((id, constant));
        }
        if let Some(other) = self.signatures.get(&signature) {
            if *other != id {
                pending.push((id, *other));
            }
        } else {
            self.signatures.insert(signature, id);
        }
        self.application_signatures.insert(id, signature);
    }

    fn close(&mut self, pending: Vec<(u64, u64)>) -> bool {
        self.close_with_affine_definition(pending, false)
    }

    fn close_with_affine_definition(
        &mut self,
        mut pending: Vec<(u64, u64)>,
        mut affine_definition: bool,
    ) -> bool {
        let mut changed = false;
        while let Some((left, right)) = pending.pop() {
            let definitional = std::mem::take(&mut affine_definition);
            crate::instrumentation::record_deterministic_work(1);
            let mut kept = self.root(left);
            let mut moved = self.root(right);
            if kept == moved {
                continue;
            }
            if self.weight(kept) < self.weight(moved) {
                std::mem::swap(&mut kept, &mut moved);
            }
            let non_affine = (!definitional && !self.address_nodes.contains(&kept))
                || self.non_affine_classes.contains(&kept)
                || self.non_affine_classes.contains(&moved);
            if non_affine {
                self.mark_non_affine(kept);
                self.mark_non_affine(moved);
            }
            if let Some(witness) = self.read_witnesses.get(&moved).cloned() {
                self.read_witnesses.remove(&moved);
                self.retain_read_witness(kept, witness);
            }
            self.merge_affine_applications(moved, kept);
            let weight = self.weight(kept) + self.weight(moved);
            self.merge_address_offsets(moved, kept, &mut pending);
            self.merge_storage_addresses(moved, kept);
            self.merge_additive_addresses(moved, kept);
            self.merge_additive_offsets(moved, kept);
            self.merge_alignment_witnesses(moved, kept);
            if let Some((lower, upper)) = self.signed_int32_intervals.get(&moved).copied() {
                crate::instrumentation::record_deterministic_work(1);
                let (kept_lower, kept_upper) = self
                    .signed_int32_intervals
                    .get(&kept)
                    .copied()
                    .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
                self.signed_int32_intervals.remove(&moved);
                self.signed_int32_intervals
                    .insert(kept, (lower.max(kept_lower), upper.min(kept_upper)));
            }
            if let Some(truth) = self.condition_truth.get(&moved).copied() {
                let kept_truth = self.condition_truth.get(&kept).copied().unwrap_or(0);
                self.condition_truth.remove(&moved);
                self.condition_truth.insert(kept, kept_truth | truth);
            }
            self.parents.insert(moved, kept);
            self.history = Some(Arc::new(MergeHistory {
                depth: self.history.as_ref().map_or(1, |node| node.depth + 1),
                merge: TermClassMerge { moved, kept },
                parent: self.history.clone(),
            }));
            self.weights.remove(&moved);
            self.weights.insert(kept, weight);
            let moved_uses = self.uses.get(&moved).cloned().unwrap_or_default();
            let mut kept_uses = self.uses.get(&kept).cloned().unwrap_or_default();
            // A class learns a literal only once. Its existing applications
            // then need constant evaluation as well as the moved applications.
            if !self.int32_constants.contains_key(&kept)
                && let Some(value) = self.int32_constants.get(&moved).copied()
            {
                self.int32_constants.insert(kept, value);
                let literal_uses = self.constant_uses.get(&kept).cloned().unwrap_or_default();
                for id in literal_uses.iter() {
                    self.reindex_application(*id, &mut pending);
                }
            }
            self.int32_constants.remove(&moved);
            if let Some(moved_literal_uses) = self.constant_uses.get(&moved).cloned() {
                self.constant_uses.remove(&moved);
                let mut kept_literal_uses =
                    self.constant_uses.get(&kept).cloned().unwrap_or_default();
                for id in moved_literal_uses.iter() {
                    crate::instrumentation::record_deterministic_work(1);
                    kept_literal_uses = kept_literal_uses.with_value(*id);
                }
                self.constant_uses.insert(kept, kept_literal_uses);
            }
            for id in moved_uses.iter() {
                crate::instrumentation::record_deterministic_work(1);
                kept_uses = kept_uses.with_value(*id);
                self.reindex_application(*id, &mut pending);
            }
            self.uses.remove(&moved);
            if !kept_uses.is_empty() {
                self.uses.insert(kept, kept_uses);
            }
            changed = true;
        }
        changed
    }
}

#[cfg(test)]
mod tests {
    use super::super::EqualityGraph;
    use super::*;
    use crate::kernel::{Bitvector32Term, ConditionTerm, Pointer, Proposition, PureFactContext};

    fn var(id: u64) -> PointerOffsetTerm {
        PointerOffsetTerm::Variable(Variable(id))
    }
    fn equality(left: &PointerOffsetTerm, right: &PointerOffsetTerm) -> ConditionTerm {
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone())
    }

    fn add(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
        // Preserve nested applications rather than folding constants here.
        PointerOffsetTerm::Add(Box::new(left), Box::new(right))
    }

    #[test]
    fn addition_congruence_handles_both_operands_and_insertion_orders() {
        for equality_first in [false, true] {
            let mut graph = EqualityGraph::default();
            let (a, b, c, d) = (var(100), var(101), var(102), var(103));
            let (left, right) = (var(104), var(105));
            if equality_first {
                graph.add_offset_equality(&a, &b);
                graph.add_offset_equality(&c, &d);
            }
            graph.add_offset_equality(&add(a.clone(), c.clone()), &left);
            graph.add_offset_equality(&add(b.clone(), d.clone()), &right);
            if !equality_first {
                assert!(!graph.are_offsets_equal(&left, &right));
                graph.add_offset_equality(&a, &b);
                assert!(!graph.are_offsets_equal(&left, &right));
                graph.add_offset_equality(&c, &d);
            }
            // Query the aliases, not the addition trees: closure must already
            // have propagated the operand equalities into their parents.
            assert!(graph.are_offsets_equal(&left, &right));
        }
    }

    #[test]
    fn addition_congruence_propagates_nested_late_merges_and_is_branch_local() {
        let nested = |mut term| {
            for i in 0..64 {
                term = add(term, var(200 + i));
            }
            term
        };
        let (a, b, left, right) = (var(110), var(111), var(112), var(113));
        let mut parent = EqualityGraph::default();
        parent.add_offset_equality(&nested(a.clone()), &left);
        parent.add_offset_equality(&nested(b.clone()), &right);
        let sibling = parent.clone();
        let mut branch = parent.clone();
        branch.add_offset_equality(&a, &b);
        assert!(branch.are_offsets_equal(&left, &right));
        assert!(!parent.are_offsets_equal(&left, &right));
        assert!(!sibling.are_offsets_equal(&left, &right));
    }

    #[test]
    fn addition_congruence_does_not_cancel_or_equate_distinct_displacements() {
        let (a, b, c) = (var(120), var(121), var(122));
        let mut graph = EqualityGraph::default();
        graph.add_offset_equality(&add(a.clone(), c.clone()), &add(b.clone(), c.clone()));
        assert!(!graph.are_offsets_equal(&a, &b));
        graph.add_offset_equality(&a, &b);
        assert!(!graph.are_offsets_equal(
            &add(a, PointerOffsetTerm::Constant(1)),
            &add(b, PointerOffsetTerm::Constant(2)),
        ));
    }

    #[test]
    fn addition_congruence_closes_cycles_without_generating_terms() {
        let a = var(130);
        let b = add(a.clone(), var(131));
        let c = add(b.clone(), var(131));
        let mut graph = EqualityGraph::default();
        assert!(!graph.are_offsets_equal(&a, &c));
        graph.add_offset_equality(&a, &b);
        assert!(graph.are_offsets_equal(&a, &c));
    }

    #[test]
    fn addition_congruence_matches_a_small_exhaustive_closure() {
        // Independent oracle for the term-class fragment: repeatedly scan
        // every pair of applications, relabeling a flat partition. The public
        // graph query additionally accepts affine equalities, so compare the
        // indexed term classes directly with this congruence-only oracle.
        let mut terms = vec![var(300), var(301), var(302)];
        let mut applications = Vec::new();
        for left in 0..3 {
            for right in 0..3 {
                applications.push((terms.len(), left, right));
                terms.push(add(terms[left].clone(), terms[right].clone()));
            }
        }
        for left in 3..12 {
            applications.push((terms.len(), left, 0));
            terms.push(add(terms[left].clone(), terms[0].clone()));
        }
        fn join(classes: &mut [usize], left: usize, right: usize) -> bool {
            let (left, right) = (classes[left], classes[right]);
            if left == right {
                return false;
            }
            for class in classes {
                if *class == right {
                    *class = left;
                }
            }
            true
        }
        for seed in 1..=4u64 {
            let mut graph = TermClasses::default();
            for term in &terms {
                assert!(graph.are_equal(term, term));
            }
            let mut classes = (0..terms.len()).collect::<Vec<_>>();
            let mut random = seed;
            for _ in 0..8 {
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                let left = (random >> 32) as usize % terms.len();
                random = random.wrapping_mul(6364136223846793005).wrapping_add(1);
                let right = (random >> 32) as usize % terms.len();
                graph.add_equality(&terms[left], &terms[right]);
                join(&mut classes, left, right);
                loop {
                    let mut changed = false;
                    for &(a, al, ar) in &applications {
                        for &(b, bl, br) in &applications {
                            if classes[al] == classes[bl] && classes[ar] == classes[br] {
                                changed |= join(&mut classes, a, b);
                            }
                        }
                    }
                    if !changed {
                        break;
                    }
                }
                for (a, left) in terms.iter().enumerate() {
                    for (b, right) in terms.iter().enumerate() {
                        assert_eq!(
                            graph.are_equal(left, right),
                            classes[a] == classes[b],
                            "seed={seed}, a={a}, b={b}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn affine_completeness_follows_only_affected_address_dependencies() {
        let base = Pointer::symbolic(Variable(895_050));
        let other = Pointer::symbolic(Variable(895_051));
        let alias = Pointer::symbolic(Variable(895_052));
        let mut graph = EqualityGraph::default();
        graph.address_class(&Pointer {
            block: base.block.clone(),
            offset: add(var(895_053), var(895_054)),
        });
        graph.address_class(&other.offset_by_bytes(8));
        let sibling = graph.clone();
        graph.add_offset_equality(&var(895_053), &var(895_055));
        assert!(!graph.affine_addresses_complete(&base.block));
        assert!(graph.affine_addresses_complete(&other.block));
        assert!(sibling.affine_addresses_complete(&base.block));
        // A newly registered parent inherits the already-affected operand.
        let late = Pointer::symbolic(Variable(895_056));
        graph.address_class(&Pointer {
            block: late.block.clone(),
            offset: add(var(895_055), var(895_057)),
        });
        assert!(!graph.affine_addresses_complete(&late.block));
        graph.add_equality(&base, &alias);
        assert!(!graph.affine_addresses_complete(&alias.block));
        assert!(graph.affine_addresses_complete(&other.block));
    }

    #[test]
    fn addition_congruence_late_merge_work_scales_with_affected_parents() {
        for size in [16u64, 64, 256, 1024] {
            let mut graph = EqualityGraph::default();
            for i in 0..size {
                graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
                graph.add_offset_equality(&add(var(1), var(10 + i)), &var(20_000 + i));
            }
            let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    graph.add_offset_equality(&var(0), &var(1));
                    for i in 0..size {
                        assert!(graph.are_offsets_equal(&var(10_000 + i), &var(20_000 + i)));
                    }
                })
            });
            let logarithm = size.ilog2() as usize + 1;
            assert!(work < 80 * size as usize, "size={size}, work={work}");
            assert!(
                map_work < 512 * size as usize * logarithm,
                "size={size}, map work={map_work}"
            );
        }
    }

    #[test]
    fn addition_congruence_forks_do_not_reindex_unrelated_parents() {
        for size in [16u64, 64, 256, 1024] {
            let mut graph = EqualityGraph::default();
            for i in 0..size {
                graph.add_offset_equality(&add(var(0), var(10 + i)), &var(10_000 + i));
            }
            let ((_, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    for i in 0..size {
                        let mut branch = graph.clone();
                        // Argument order must not move the class with many
                        // parents under this newly registered singleton.
                        branch.add_offset_equality(&var(20_000 + i), &var(0));
                        assert!(
                            branch.are_offsets_equal(&add(var(20_000 + i), var(10)), &var(10_000))
                        );
                    }
                })
            });
            let logarithm = size.ilog2() as usize + 1;
            assert!(work < 100 * size as usize, "size={size}, work={work}");
            assert!(
                map_work < 512 * size as usize * logarithm,
                "size={size}, map work={map_work}"
            );
            assert!(!graph.are_offsets_equal(&var(20_000), &var(0)));
        }
    }

    #[test]
    fn offset_equality_is_transitive_symmetric_and_branch_local() {
        let (a, b, c) = (var(1), var(2), var(3));
        let mut parent = EqualityGraph::default();
        parent.add_offset_equality(&a, &b);
        let mut branch = parent.clone();
        branch.add_offset_equality(&b, &c);
        assert!(branch.are_offsets_equal(&c, &a));
        assert!(branch.are_offsets_equal(&a, &a));
        assert!(!parent.are_offsets_equal(&a, &c));
        let plus_one =
            |x| PointerOffsetTerm::Add(Box::new(x), Box::new(PointerOffsetTerm::Constant(1)));
        assert!(branch.are_offsets_equal(&plus_one(a), &plus_one(c)));
    }

    #[test]
    fn offset_equality_preserves_width_signedness_and_snapshot_identity() {
        let _session = crate::kernel::VerificationSession::enter();
        let scaled = |value, width, unsigned| PointerOffsetTerm::Int64Scaled {
            value: Box::new(value),
            byte_width: width,
            unsigned,
        };
        let value = Bitvector32Term::Variable(Variable(10));
        let signed = scaled(value.clone(), 4, false);
        let target = var(11);
        let mut graph = EqualityGraph::default();
        graph.add_offset_equality(&signed, &target);
        assert!(!graph.are_offsets_equal(&scaled(value.clone(), 8, false), &target));
        assert!(!graph.are_offsets_equal(&scaled(value, 4, true), &target));
        let before =
            crate::kernel::intern_c_memory(crate::kernel::CMemory::new().with_block("offset", 8));
        let address = Pointer::symbolic(Variable(12));
        let after = crate::kernel::intern_c_memory(before.memory().clone().store(
            address.clone(),
            crate::kernel::CValue::Int32(Bitvector32Term::Constant(9)),
        ));
        let load = |memory: &crate::kernel::SharedCMemory| {
            Bitvector32Term::Variable(crate::kernel::load_variable_for_cell_with_origin(
                memory,
                &address,
                crate::kernel::LoadKind::Bits32,
                8,
                memory,
            ))
        };
        let old = scaled(load(&before), 4, false);
        let new = scaled(load(&after), 4, false);
        graph.add_offset_equality(&old, &target);
        assert!(!graph.are_offsets_equal(&new, &target));
        assert!(!graph.are_offsets_equal(&add(new, var(13)), &add(target, var(13))));
    }

    #[test]
    fn offset_context_withdrawal_and_restriction_preserve_only_retained_equalities() {
        let (a, b, c) = (var(20), var(21), var(22));
        let ab = equality(&a, &b);
        let bc = equality(&b, &c);
        let p = Pointer::symbolic(Variable(23));
        let q = Pointer::symbolic(Variable(24));
        let pq = ConditionTerm::pointer_equal(p.clone(), q.clone());
        let context = PureFactContext::new()
            .assume_condition(ab.clone(), true)
            .assume_condition(bc.clone(), true)
            .assume_condition(pq.clone(), true);
        assert!(context.equality_graph.are_offsets_equal(&a, &c));
        let translated_a = add(a.clone(), var(25));
        let translated_c = add(c.clone(), var(25));
        assert!(
            context
                .equality_graph
                .are_offsets_equal(&translated_a, &translated_c)
        );
        let weakened = context.without_exact_fact(&Proposition::ConditionIs(bc.clone(), true));
        assert!(!weakened.equality_graph.are_offsets_equal(&a, &c));
        assert!(
            !weakened
                .equality_graph
                .are_offsets_equal(&translated_a, &translated_c)
        );
        assert!(weakened.equality_graph.are_offsets_equal(&a, &b));
        assert!(weakened.equality_graph.are_equal(&p, &q));
        let no_pointer = context.without_exact_fact(&Proposition::ConditionIs(pq, true));
        assert!(!no_pointer.equality_graph.are_equal(&p, &q));
        assert!(no_pointer.equality_graph.are_offsets_equal(&a, &c));
        let restricted = context.restricted_to_facts(&[(ab, true)], &[]);
        assert!(!restricted.equality_graph.are_offsets_equal(&a, &c));
        assert!(restricted.equality_graph.are_offsets_equal(&a, &b));
        let reversed = context.clone().assume_condition(bc, false);
        assert!(!reversed.equality_graph.are_offsets_equal(&a, &c));
        assert!(context.equality_graph.are_offsets_equal(&a, &c));
    }

    #[test]
    fn offset_withdrawal_keeps_a_separately_stated_reverse_equality() {
        let (a, b, c) = (var(30), var(31), var(32));
        let ab = equality(&a, &b);
        let ba = equality(&b, &a);
        let context = PureFactContext::new()
            .assume_condition(ab.clone(), true)
            .assume_condition(ba.clone(), true)
            .assume_condition(equality(&b, &c), true);
        let once = context.without_exact_fact(&Proposition::ConditionIs(ab, true));
        assert!(once.equality_graph.are_offsets_equal(&a, &c));
        let twice = once.without_exact_fact(&Proposition::ConditionIs(ba, true));
        assert!(!twice.equality_graph.are_offsets_equal(&a, &c));
        assert!(twice.equality_graph.are_offsets_equal(&b, &c));
    }

    #[test]
    fn offset_graph_construction_and_fork_queries_scale_with_indexed_work() {
        let offset = |id| PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(id))),
            byte_width: 4,
        };
        for size in [16u64, 64, 256, 1024] {
            let ((graph, work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let mut graph = EqualityGraph::default();
                    for i in 0..size {
                        graph.add_offset_equality(&offset(i), &offset(i + 1));
                        assert!(graph.are_offsets_equal(&offset(0), &offset(i + 1)));
                    }
                    graph
                })
            });
            let logarithm = size.ilog2() as usize + 1;
            assert!(work < 40 * size as usize, "size={size}, work={work}");
            assert!(
                map_work < 160 * size as usize * logarithm,
                "size={size}, map work={map_work}"
            );
            let (_, fork_work) = crate::persistent::measure_persistent_work(|| {
                let mut branch = graph.clone();
                branch.add_offset_equality(&offset(size), &offset(size + 1));
                assert!(branch.are_offsets_equal(&offset(0), &offset(size + 1)));
                assert!(!graph.are_offsets_equal(&offset(0), &offset(size + 1)));
            });
            assert!(
                fork_work < 160 * logarithm,
                "size={size}, fork work={fork_work}"
            );
        }
    }
}
