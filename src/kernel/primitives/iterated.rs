//! Iterated guarded ownership: one resource fact for a bounded family of
//! element ranges, each held exactly when a guard cell says so.
//!
//! `forall (k: int32) where lo <= k and k < hi { if g[k] == v { owns
//! base[s * k + a..s * k + b]; } }` in a resource body lowers to one
//! [`CIteratedMemory`]. The fact is never enumerated: every question about one
//! element is answered from the index's range membership and the guard cell's
//! value at that index, read from the current memory.
//!
//! The fact denotes the separating conjunction, over every index `k` in
//! `lo..hi` that is not a hole, of `base[s * k + a..s * k + b]` when the guard
//! holds at `k` and of nothing when it does not. A hole is an index whose
//! element the proof has taken out (`take`) or whose guard a C store has just
//! changed from false; the fact makes no claim about a hole. The checked
//! operations that change holes, and the store rule that keeps the guard
//! honest while the fact is held, are in `crate::kernel::iterated`.

use super::*;

/// The guard cell array and the comparison that selects an index.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CIteratedGuard {
    /// Address of the guard cell at index 0.
    pub(in crate::kernel) base: Pointer,
    /// The C type of one guard cell (its loads are read at this type).
    pub(in crate::kernel) cell_type: CType,
    /// The byte width of one guard cell.
    pub(in crate::kernel) cell_width: u32,
    /// `true` for `g[k] == value`, `false` for `g[k] != value`.
    pub(in crate::kernel) holds_when_equal: bool,
    pub(in crate::kernel) value: Bitvector32Term,
}

/// The name of the resource definition whose clause formed a fact. It is
/// presentation only: two definitions that declare the same clause over the
/// same cells denote the same holding, so the label takes no part in
/// equality, ordering, or hashing (as `CExpressionLoadSource` does not).
#[derive(Clone, Debug)]
pub struct IteratedOwnerLabel(Arc<str>);

impl PartialEq for IteratedOwnerLabel {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl Eq for IteratedOwnerLabel {}

impl std::hash::Hash for IteratedOwnerLabel {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

impl Ord for IteratedOwnerLabel {
    fn cmp(&self, _other: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}

impl PartialOrd for IteratedOwnerLabel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// One held iterated-ownership fact.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct CIteratedMemory {
    /// The resource definition whose body declared the clause the fact was
    /// formed from, for diagnostics only.
    pub(in crate::kernel) owner: IteratedOwnerLabel,
    /// Address of element index 0's base (the clause's `base`).
    pub(in crate::kernel) element_base: Pointer,
    /// Byte width of one logical element of `base`.
    pub(in crate::kernel) element_width: u32,
    /// Element `k` covers `base[stride * k + start_offset..stride * k +
    /// end_offset]`; validation guarantees `0 < end_offset - start_offset <=
    /// stride`, so distinct indices never overlap.
    pub(in crate::kernel) stride: u32,
    pub(in crate::kernel) start_offset: i32,
    pub(in crate::kernel) end_offset: i32,
    pub(in crate::kernel) lower: Bitvector32Term,
    pub(in crate::kernel) upper: Bitvector32Term,
    pub(in crate::kernel) guard: CIteratedGuard,
    /// Indices about which the fact currently makes no claim, in the order
    /// they were opened. Only explicit proof steps and checked C stores add
    /// one, so the list is bounded by the proof's own operations.
    pub(in crate::kernel) holes: Arc<[Bitvector32Term]>,
}

impl CIteratedMemory {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        owner: &str,
        element_base: Pointer,
        element_width: u32,
        stride: u32,
        start_offset: i32,
        end_offset: i32,
        lower: Bitvector32Term,
        upper: Bitvector32Term,
        guard: CIteratedGuard,
    ) -> Option<Self> {
        if stride == 0
            || element_width == 0
            || guard.cell_width == 0
            || end_offset <= start_offset
            || i64::from(end_offset) - i64::from(start_offset) > i64::from(stride)
        {
            return None;
        }
        Some(Self {
            owner: IteratedOwnerLabel(Arc::from(owner)),
            element_base,
            element_width,
            stride,
            start_offset,
            end_offset,
            lower,
            upper,
            guard,
            holes: Arc::from(Vec::new()),
        })
    }

    pub fn owner(&self) -> &str {
        &self.owner.0
    }

    pub fn element_base(&self) -> &Pointer {
        &self.element_base
    }

    pub fn element_width(&self) -> u32 {
        self.element_width
    }

    pub fn lower(&self) -> &Bitvector32Term {
        &self.lower
    }

    pub fn upper(&self) -> &Bitvector32Term {
        &self.upper
    }

    pub fn guard(&self) -> &CIteratedGuard {
        &self.guard
    }

    pub fn holes(&self) -> &[Bitvector32Term] {
        &self.holes
    }

    /// The element index expressed in the clause's range coordinates.
    fn scaled(&self, index: &Bitvector32Term, offset: i32) -> Bitvector32Term {
        Bitvector32Term::add(
            Bitvector32Term::multiply(index.clone(), Bitvector32Term::Constant(self.stride)),
            Bitvector32Term::Constant(offset as u32),
        )
    }

    /// The memory range element `index` covers.
    pub(crate) fn element_range(&self, index: &Bitvector32Term) -> CMemoryRange {
        CMemoryRange::new_with_element_width(
            self.element_base.clone(),
            self.scaled(index, self.start_offset),
            self.scaled(index, self.end_offset),
            self.element_width,
        )
    }

    /// The memory range spanned by every element of `lo..hi`, when the
    /// elements tile it without gaps (`end_offset - start_offset ==
    /// stride`). This is the range `gather` consumes and `scatter` produces.
    pub(crate) fn covering_range(&self) -> Option<CMemoryRange> {
        (i64::from(self.end_offset) - i64::from(self.start_offset) == i64::from(self.stride)).then(
            || {
                CMemoryRange::new_with_element_width(
                    self.element_base.clone(),
                    self.scaled(&self.lower, self.start_offset),
                    self.scaled(&self.upper, self.start_offset),
                    self.element_width,
                )
            },
        )
    }

    /// The address of the guard cell at `index`.
    pub(crate) fn guard_cell(&self, index: &Bitvector32Term) -> Pointer {
        self.guard
            .base
            .offset_by_elements(index.clone(), self.guard.cell_width)
    }

    /// The guard cells of every index in the range.
    pub(crate) fn guard_range(&self) -> CMemoryRange {
        CMemoryRange::new_with_element_width(
            self.guard.base.clone(),
            self.lower.clone(),
            self.upper.clone(),
            self.guard.cell_width,
        )
    }

    pub(crate) fn with_hole(&self, index: Bitvector32Term) -> Self {
        let mut holes = self.holes.to_vec();
        holes.push(index);
        Self {
            holes: Arc::from(holes),
            ..self.clone()
        }
    }

    pub(crate) fn without_hole_at(&self, position: usize) -> Self {
        let mut holes = self.holes.to_vec();
        holes.remove(position);
        Self {
            holes: Arc::from(holes),
            ..self.clone()
        }
    }

    /// The same fact with every term rewritten by `term` and every pointer by
    /// `pointer`. Substitution, canonicalization, and snapshot rewriting use
    /// this so that every term the fact carries is visited exactly once.
    pub(crate) fn map_terms(
        &self,
        mut term: impl FnMut(&Bitvector32Term) -> Bitvector32Term,
        mut pointer: impl FnMut(&Pointer) -> Pointer,
    ) -> Self {
        Self {
            owner: self.owner.clone(),
            element_base: pointer(&self.element_base),
            element_width: self.element_width,
            stride: self.stride,
            start_offset: self.start_offset,
            end_offset: self.end_offset,
            lower: term(&self.lower),
            upper: term(&self.upper),
            guard: CIteratedGuard {
                base: pointer(&self.guard.base),
                cell_type: self.guard.cell_type,
                cell_width: self.guard.cell_width,
                holds_when_equal: self.guard.holds_when_equal,
                value: term(&self.guard.value),
            },
            holes: self.holes.iter().map(&mut term).collect::<Vec<_>>().into(),
        }
    }

    /// Every bitvector term the fact carries, pointers' offsets excluded.
    pub(crate) fn terms(&self) -> impl Iterator<Item = &Bitvector32Term> {
        [&self.lower, &self.upper, &self.guard.value]
            .into_iter()
            .chain(self.holes.iter())
    }

    /// Both pointers the fact carries.
    pub(crate) fn pointers(&self) -> [&Pointer; 2] {
        [&self.element_base, &self.guard.base]
    }

    /// The two blocks the fact's denotation depends on.
    pub(crate) fn blocks(&self) -> [&PointerBlock; 2] {
        [&self.element_base.block, &self.guard.base.block]
    }
}

impl CIteratedGuard {
    pub(crate) fn new(
        base: Pointer,
        cell_type: CType,
        cell_width: u32,
        holds_when_equal: bool,
        value: Bitvector32Term,
    ) -> Self {
        Self {
            base,
            cell_type,
            cell_width,
            holds_when_equal,
            value,
        }
    }

    pub fn base(&self) -> &Pointer {
        &self.base
    }

    pub fn holds_when_equal(&self) -> bool {
        self.holds_when_equal
    }

    pub fn value(&self) -> &Bitvector32Term {
        &self.value
    }
}

impl CIteratedSpec {
    /// Every C expression the clause carries: the element base, the index
    /// bounds, the guard base, and the guard value.
    pub(crate) fn expressions(&self) -> [&CExpression; 5] {
        [
            &self.element.base,
            &self.element.start,
            &self.element.end,
            &self.guard_base,
            &self.guard_value,
        ]
    }

    /// The same clause with every expression rewritten by `rewrite`.
    pub(crate) fn map_expressions(
        &self,
        mut rewrite: impl FnMut(&CExpression) -> CExpression,
    ) -> Self {
        Self {
            owner: self.owner.clone(),
            element: CMemorySegment {
                base: rewrite(&self.element.base),
                start: rewrite(&self.element.start),
                end: rewrite(&self.element.end),
                element_width: self.element.element_width,
                guard: self.element.guard.clone(),
            },
            stride: self.stride,
            start_offset: self.start_offset,
            end_offset: self.end_offset,
            guard_base: rewrite(&self.guard_base),
            guard_cell_type: self.guard_cell_type,
            guard_cell_width: self.guard_cell_width,
            holds_when_equal: self.holds_when_equal,
            guard_value: rewrite(&self.guard_value),
        }
    }

    pub(crate) fn expressions_mut(&mut self) -> [&mut CExpression; 5] {
        [
            &mut self.element.base,
            &mut self.element.start,
            &mut self.element.end,
            &mut self.guard_base,
            &mut self.guard_value,
        ]
    }
}
