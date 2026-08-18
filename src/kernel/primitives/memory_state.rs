use super::*;

pub(super) fn resource_context_has_symbolic_int32_range_read(
    resources: &ResourceContext,
    base: &Pointer,
    bytes: &Bitvector32Term,
) -> bool {
    resources.facts().iter().any(|fact| {
        let Some(range) = fact.memory_range() else {
            return false;
        };
        let range_base = range.base().offset_by_int32_elements(range.start().clone());
        let range_bytes = Bitvector32Term::multiply(
            Bitvector32Term::subtract(range.end().clone(), range.start().clone()),
            Bitvector32Term::Constant(4),
        );
        &range_base == base && &range_bytes == bytes
    })
}

impl CLocalEnvironment {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.set(name, value);
        self
    }

    pub fn with_typed(mut self, name: impl Into<String>, value: CValue, c_type: CType) -> Self {
        self.set_typed(name, value, c_type);
        self
    }

    pub fn with_int32_array(mut self, name: impl Into<String>, length: u32) -> Self {
        self.set_int32_array(name, length);
        self
    }

    pub fn set(&mut self, name: impl Into<String>, value: CValue) {
        let c_type = value.c_type();
        self.set_typed(name, value, c_type);
    }

    pub fn set_typed(&mut self, name: impl Into<String>, value: CValue, c_type: CType) {
        std::sync::Arc::make_mut(&mut self.bindings)
            .insert(name.into(), CLocalBinding::Object { value, c_type });
    }

    pub(in crate::kernel) fn set_uninitialized(&mut self, name: impl Into<String>, c_type: CType) {
        std::sync::Arc::make_mut(&mut self.bindings)
            .insert(name.into(), CLocalBinding::UninitializedObject { c_type });
    }

    pub fn set_int32_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::Int32, length);
    }

    pub fn set_uint8_array(&mut self, name: impl Into<String>, length: u32) {
        self.set_array_object(name, CType::UInt8, length);
    }

    pub(in crate::kernel) fn set_array_object(
        &mut self,
        name: impl Into<String>,
        element_type: CType,
        length: u32,
    ) {
        std::sync::Arc::make_mut(&mut self.bindings).insert(
            name.into(),
            CLocalBinding::ArrayObject {
                element_type,
                length,
            },
        );
    }

    pub fn get(&self, name: &str) -> Option<&CValue> {
        match self.bindings.get(name) {
            Some(CLocalBinding::Object { value, .. }) => Some(value),
            Some(CLocalBinding::UninitializedObject { .. })
            | Some(CLocalBinding::ArrayObject { .. })
            | None => None,
        }
    }

    /// Exact name membership, including arrays and uninitialized objects.
    /// Proof-local binders use this indexed query to reject shadowing without
    /// materializing or scanning the complete local environment.
    pub fn contains_name(&self, name: &str) -> bool {
        self.bindings.contains_key(name)
    }

    pub fn object_values(&self) -> impl Iterator<Item = (&str, &CValue)> {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::Object { value, .. } => Some((name.as_str(), value)),
                CLocalBinding::UninitializedObject { .. } | CLocalBinding::ArrayObject { .. } => {
                    None
                }
            })
    }

    pub fn array_object_values(&self) -> impl Iterator<Item = (&str, CValue, CType)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::ArrayObject { element_type, .. } => Some((
                    name.as_str(),
                    CValue::Pointer(CMemory::local_pointer(name)),
                    *element_type,
                )),
                CLocalBinding::Object { .. } | CLocalBinding::UninitializedObject { .. } => None,
            })
    }

    pub(in crate::kernel) fn object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            None => None,
        }
    }

    pub(in crate::kernel) fn scalar_object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { .. }) | None => None,
        }
    }

    pub(in crate::kernel) fn binding(&self, name: &str) -> Option<&CLocalBinding> {
        self.bindings.get(name)
    }

    pub(in crate::kernel) fn is_array_object(&self, name: &str) -> bool {
        matches!(self.binding(name), Some(CLocalBinding::ArrayObject { .. }))
    }
}

impl CBlock {
    pub fn new(size: u32) -> Self {
        Self {
            size: Bitvector32Term::Constant(size),
        }
    }

    pub(in crate::kernel) fn with_symbolic_size(size: Bitvector32Term) -> Self {
        Self { size }
    }

    pub fn size(&self) -> &Bitvector32Term {
        &self.size
    }
}

fn heap_allocation_may_contain_pointer(base: &Pointer, pointer: &Pointer) -> bool {
    if base.block != pointer.block {
        return false;
    }
    if base.block != PointerBlock::ExternalArgument {
        return true;
    }

    if pointer.offset == base.offset {
        return true;
    }

    fn contains_base_offset(term: &PointerOffsetTerm, base: &PointerOffsetTerm) -> bool {
        match term {
            PointerOffsetTerm::Add(left, right) => {
                left.as_ref() == base
                    || right.as_ref() == base
                    || contains_base_offset(left, base)
                    || contains_base_offset(right, base)
            }
            PointerOffsetTerm::Constant(_)
            | PointerOffsetTerm::Variable(_)
            | PointerOffsetTerm::Int32Scaled { .. } => false,
        }
    }

    contains_base_offset(&pointer.offset, &base.offset)
}

impl CMemory {
    pub fn new() -> Self {
        Self::default()
    }

    pub(crate) fn has_same_snapshot_markers(&self, other: &Self) -> bool {
        self.blocks == other.blocks && self.heap == other.heap
    }

    pub fn with_block(mut self, block: impl Into<PointerBlock>, size: u32) -> Self {
        let block = block.into();
        // Havoc marker blocks mean "the state may have changed", never "a
        // fresh block appeared"; recording a benign block-declaration edge
        // for one would launder the havoc (conventions.md's soundness trap,
        // pinned by `conditions_equal_modulo_proven_snapshots_needs_frame_
        // evidence`). The havoc producers insert their markers directly,
        // but tests and any future caller may spell them through this
        // constructor, so the refusal lives here.
        if memory_dag_disabled() || block.starts_with("havoc:") || block.starts_with("call-havoc:")
        {
            std::sync::Arc::make_mut(&mut self.blocks).insert(block, CBlock::new(size));
            return self;
        }
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::new(size));
        record_c_memory_derivation(&self, CMemoryDerivation::BlockDeclared { base, block });
        self
    }

    pub(in crate::kernel) fn free_heap_block(
        mut self,
        pointer: &Pointer,
    ) -> Result<Self, CInvalidFree> {
        if self.heap.retired_allocations.contains_key(pointer) {
            return Err(CInvalidFree::DoubleFree);
        }
        let Some(bytes) = std::sync::Arc::make_mut(&mut self.heap)
            .live_allocations
            .remove(pointer)
        else {
            return Err(
                if self
                    .heap
                    .live_allocations
                    .keys()
                    .any(|base| heap_allocation_may_contain_pointer(base, pointer))
                {
                    CInvalidFree::InteriorPointer
                } else {
                    CInvalidFree::NonHeapPointer
                },
            );
        };
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        if pointer.block != PointerBlock::ExternalArgument {
            std::sync::Arc::make_mut(&mut self.blocks).remove(&pointer.block);
        }
        std::sync::Arc::make_mut(&mut self.heap)
            .retired_allocations
            .insert(pointer.clone(), bytes.clone());
        std::sync::Arc::make_mut(&mut self.heap)
            .uninitialized_allocations
            .remove(pointer);
        std::sync::Arc::make_mut(&mut self.cells)
            .retain(|cell, _| !heap_allocation_may_contain_pointer(pointer, cell));
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::HeapFreed {
                    base,
                    allocation_base: pointer.clone(),
                    bytes: bytes.clone(),
                },
            );
        }
        Ok(self)
    }

    pub(in crate::kernel) fn live_heap_block_size(
        &self,
        pointer: &Pointer,
    ) -> Option<&Bitvector32Term> {
        self.heap.live_allocations.get(pointer)
    }

    pub(crate) fn is_live_heap_address(&self, pointer: &Pointer) -> bool {
        self.heap
            .live_allocations
            .keys()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
    }

    pub(in crate::kernel) fn heap_live_allocation_bases(&self) -> impl Iterator<Item = &Pointer> {
        self.heap.live_allocations.keys()
    }

    pub(in crate::kernel) fn is_uninitialized_heap_address(&self, pointer: &Pointer) -> bool {
        self.heap
            .uninitialized_allocations
            .iter()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
    }

    pub(in crate::kernel) fn is_retired_heap_address(&self, pointer: &Pointer) -> bool {
        self.heap
            .retired_allocations
            .keys()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
    }

    /// Registers the exact base named by an allocation contract. Unlike a
    /// fresh `malloc`, this does not create a concrete block or imply that its
    /// existing bytes are uninitialized; access remains governed by the
    /// accompanying memory resources.
    pub(in crate::kernel) fn with_heap_allocation_claim(
        mut self,
        base: Pointer,
        bytes: impl Into<Bitvector32Term>,
    ) -> Option<Self> {
        let bytes = bytes.into();
        if bytes.as_const() == Some(0) || self.heap.retired_allocations.contains_key(&base) {
            return None;
        }
        match self.heap.live_allocations.get(&base) {
            Some(existing) if existing != &bytes => None,
            Some(_) => Some(self),
            None => {
                std::sync::Arc::make_mut(&mut self.heap)
                    .live_allocations
                    .insert(base, bytes);
                Some(self)
            }
        }
    }

    pub(in crate::kernel) fn with_pending_heap_allocation(
        mut self,
        base: Pointer,
        bytes: Bitvector32Term,
    ) -> Self {
        let prior = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .insert(base.clone(), bytes.clone());
        if let Some(prior) = prior {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::HeapAllocationPending {
                    base: prior,
                    allocation_base: base,
                    bytes,
                },
            );
        }
        self
    }

    /// Whether execution still owns the unresolved success/failure choice of
    /// a fresh heap allocation. Proof-frontier branch selection uses this
    /// read-only query to avoid duplicating that independent path split.
    pub(crate) fn has_pending_heap_allocation(&self) -> bool {
        !self.heap.pending_allocations.is_empty()
    }

    pub(in crate::kernel) fn heap_identity_in_use(&self, identity: u64) -> bool {
        self.blocks.contains_key(&PointerBlock::Heap(identity))
            || self
                .heap
                .retired_allocations
                .keys()
                .any(|base| base.block == PointerBlock::Heap(identity))
            || self
                .heap
                .pending_allocations
                .keys()
                .any(|base| base.block == PointerBlock::Symbolic(Variable(identity)))
    }

    pub(in crate::kernel) fn resolve_pending_heap_allocation(
        mut self,
        base: &Pointer,
        succeeds: bool,
    ) -> Option<(Self, Bitvector32Term, Pointer)> {
        let prior = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        let bytes = std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .remove(base)?;
        let resolved_base = if succeeds {
            let PointerBlock::Symbolic(Variable(identity)) = base.block else {
                return None;
            };
            Pointer {
                block: PointerBlock::Heap(identity),
                offset: PointerOffsetTerm::Constant(0),
            }
        } else {
            Pointer::null()
        };
        if succeeds {
            std::sync::Arc::make_mut(&mut self.blocks).insert(
                resolved_base.block.clone(),
                CBlock::with_symbolic_size(bytes.clone()),
            );
            std::sync::Arc::make_mut(&mut self.heap)
                .live_allocations
                .insert(resolved_base.clone(), bytes.clone());
            std::sync::Arc::make_mut(&mut self.heap)
                .uninitialized_allocations
                .insert(resolved_base.clone());
            if let Some(prior) = prior {
                record_c_memory_derivation(
                    &self,
                    CMemoryDerivation::HeapAllocated {
                        base: prior,
                        block: resolved_base.block.clone(),
                        bytes: bytes.clone(),
                    },
                );
            }
        }
        Some((self, bytes, resolved_base))
    }

    pub(in crate::kernel) fn with_loop_memory_havoc(
        mut self,
        variable: Variable,
        preserved_blocks: &BTreeSet<PointerBlock>,
    ) -> Self {
        // A loop body that may write memory can clobber, through some
        // pointer, any cell it can reach. Drop concrete cells outside the
        // preserved (scalar stack local) blocks so loop-head and post-loop
        // reads do not observe stale pre-loop values; anything that must
        // survive the loop has to be restated as a loop invariant. The
        // marker block additionally defeats symbolic cross-loop load
        // equality for the remaining symbolic memory.
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        std::sync::Arc::make_mut(&mut self.cells)
            .retain(|pointer, _| preserved_blocks.contains(&pointer.block));
        std::sync::Arc::make_mut(&mut self.blocks)
            .insert(format!("havoc:{}", variable.0).into(), CBlock::new(0));
        if let Some(base) = base {
            record_c_memory_derivation(&self, CMemoryDerivation::LoopHavoc { base, variable });
        }
        self
    }

    pub(in crate::kernel) fn with_call_memory_havoc(
        mut self,
        variable: Variable,
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
    ) -> Self {
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(&self));
        std::sync::Arc::make_mut(&mut self.cells).retain(|pointer, _| {
            pointer.block.starts_with("local:")
                || assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        // The marker size fingerprints the write set. Marker names restart
        // per claim verification, so two claims' snapshots can be
        // alpha-identical while their same-named havocs wrote different
        // ranges; content-addressed interning would then merge them and
        // first-wins derivation recording would let one world's edges answer
        // the other's load queries. Folding the ranges into the marker's
        // otherwise-unused size keeps such snapshots content-distinct, while
        // havocs with equal parents and equal write sets — genuinely
        // indistinguishable — still share a node. Deterministic: the hasher
        // is fixed-key and the ranges are replay-stable.
        let write_set_fingerprint = {
            use std::hash::{Hash, Hasher};
            // The fingerprint must identify the write set across the replay
            // and the independent certification, which spell one call's
            // ranges over different snapshot variants — so it hashes only
            // spelling-invariant structure: the range count, each base
            // block, and constant endpoints. That is enough to separate
            // alpha-colliding call sequences whose havocs wrote different
            // shapes; the full claim-scoped salt design is recorded in the
            // issue for the residual same-shape collisions.
            let mut shape = mutable_ranges
                .iter()
                .map(|range| {
                    (
                        format!("{:?}", range.base().block),
                        range.start().as_const(),
                        range.end().as_const(),
                    )
                })
                .collect::<Vec<_>>();
            shape.sort();
            let mut hasher = std::hash::DefaultHasher::new();
            shape.hash(&mut hasher);
            (hasher.finish() as u32) | 1
        };
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("call-havoc:{}", variable.0).into(),
            CBlock::new(write_set_fingerprint),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::CallHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.to_vec(),
                },
            );
        }
        self
    }

    pub fn store(mut self, pointer: Pointer, value: CValue) -> Self {
        if memory_dag_disabled() {
            std::sync::Arc::make_mut(&mut self.cells).insert(pointer, value);
            return self;
        }
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer.clone(), value.clone());
        record_c_memory_derivation(
            &self,
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
            },
        );
        self
    }

    pub fn load(&self, pointer: &Pointer) -> CExpressionOutcome {
        match self.cells.get(pointer) {
            Some(value) => CExpressionOutcome::Value(value.clone()),
            None => CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
        }
    }

    pub fn differing_cell_pointers(&self, other: &Self) -> Vec<Pointer> {
        let mut pointers = self.cells.keys().cloned().collect::<BTreeSet<_>>();
        pointers.extend(other.cells.keys().cloned());
        pointers
            .into_iter()
            .filter(|pointer| self.cells.get(pointer) != other.cells.get(pointer))
            .collect()
    }

    pub(in crate::kernel) fn known_value(&self, pointer: &Pointer) -> Option<CValue> {
        self.cells.get(pointer).cloned()
    }

    pub(in crate::kernel) fn without_cell(&self, pointer: &Pointer) -> Self {
        let mut memory = self.clone();
        std::sync::Arc::make_mut(&mut memory.cells).remove(pointer);
        memory
    }

    pub(in crate::kernel) fn without_possible_aliasing_cells(
        &self,
        pointer: &Pointer,
        assumptions: &PureFactContext,
    ) -> Self {
        let normalized_pointer = Pointer {
            block: pointer.block.clone(),
            offset: normalize_exact_memory_loads_in_pointer_offset(&pointer.offset, assumptions, 0),
        };
        let base = (!memory_dag_disabled()).then(|| intern_c_memory_ref(self));
        let mut memory = self.clone();
        std::sync::Arc::make_mut(&mut memory.cells).retain(|cell_pointer, _| {
            let normalized_cell_pointer = Pointer {
                block: cell_pointer.block.clone(),
                offset: normalize_exact_memory_loads_in_pointer_offset(
                    &cell_pointer.offset,
                    assumptions,
                    0,
                ),
            };
            pointers_proven_distinct_for_memory_resolution(
                &normalized_cell_pointer,
                &normalized_pointer,
                assumptions,
            )
        });
        if let Some(base) = base {
            record_c_memory_derivation(&memory, CMemoryDerivation::CellsForgotten { base });
        }
        memory
    }

    pub(in crate::kernel) fn local_pointer(name: &str) -> Pointer {
        Pointer {
            block: format!("local:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn has_block(&self, block: &PointerBlock) -> bool {
        self.blocks.contains_key(block)
    }

    pub(in crate::kernel) fn is_loadable_concretely(
        &self,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.cells
            .get(pointer)
            .is_some_and(|value| value.byte_width() == byte_width)
    }

    pub(in crate::kernel) fn can_store_concretely(
        &self,
        pointer: &Pointer,
        value: &CValue,
    ) -> bool {
        self.cells.contains_key(pointer) || self.access_in_bounds(pointer, value.byte_width())
    }

    pub(in crate::kernel) fn access_in_bounds(&self, pointer: &Pointer, byte_width: u32) -> bool {
        let Some(offset) = pointer.offset.as_const() else {
            return false;
        };
        let Ok(offset) = u32::try_from(offset) else {
            return false;
        };
        let Some(block) = self.blocks.get(&pointer.block) else {
            return false;
        };
        let Some(block_size) = block.size().as_const() else {
            return false;
        };
        offset
            .checked_add(byte_width)
            .is_some_and(|end| end <= block_size)
    }

    pub(in crate::kernel) fn symbolic_int32_load(&self, pointer: &Pointer) -> CValue {
        int32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_uint8_load(&self, pointer: &Pointer) -> CValue {
        uint8(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_pointer_load(
        &self,
        pointer: &Pointer,
        pointee_byte_width: u32,
    ) -> CValue {
        CValue::Pointer(Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(self.clone()),
                    Box::new(pointer.clone()),
                ),
                i64::from(pointee_byte_width),
            ),
        })
    }
}

impl CState {
    pub fn new() -> Self {
        Self::default()
    }

    #[cfg(test)]
    pub(crate) fn shares_nonlocal_storage_with(&self, other: &Self) -> bool {
        std::sync::Arc::ptr_eq(&self.memory.blocks, &other.memory.blocks)
            && std::sync::Arc::ptr_eq(&self.memory.cells, &other.memory.cells)
            && std::sync::Arc::ptr_eq(&self.memory.heap, &other.memory.heap)
            && self.resources.shares_storage_with(&other.resources)
            && std::sync::Arc::ptr_eq(&self.counted_populations, &other.counted_populations)
    }

    pub fn with_local(mut self, name: impl Into<String>, value: CValue) -> Self {
        self.locals.set(name, value);
        self
    }

    pub fn with_int32_array_local(mut self, name: impl Into<String>, length: u32) -> Self {
        self.locals.set_int32_array(name, length);
        self
    }

    pub fn with_memory(mut self, memory: CMemory) -> Self {
        self.memory = memory;
        self
    }

    pub fn with_resource_context(mut self, resources: ResourceContext) -> Self {
        self.resources = resources;
        self
    }

    pub fn locals(&self) -> &CLocalEnvironment {
        &self.locals
    }

    pub(crate) fn local_object_type(&self, name: &str) -> Option<CType> {
        self.locals.object_type(name)
    }

    pub fn memory(&self) -> &CMemory {
        &self.memory
    }

    pub fn resources(&self) -> &ResourceContext {
        &self.resources
    }

    pub fn with_counted_population(
        mut self,
        name: impl Into<String>,
        arguments: Vec<CValue>,
        count: Bitvector32Term,
    ) -> Self {
        let name = name.into();
        if let Some(population) = std::sync::Arc::make_mut(&mut self.counted_populations)
            .iter_mut()
            .find(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments == arguments
            })
        {
            population.count = count;
        } else {
            std::sync::Arc::make_mut(&mut self.counted_populations).push(CCountedPopulation {
                name,
                arguments,
                count,
                family_observation_marker: false,
            });
        }
        self
    }

    pub fn counted_population(&self, name: &str, arguments: &[CValue]) -> Option<&Bitvector32Term> {
        self.counted_populations
            .iter()
            .find(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments == arguments
            })
            .map(|population| &population.count)
    }

    pub fn counted_population_proven_equal(
        &self,
        name: &str,
        arguments: &[CValue],
        assumptions: &PureFactContext,
    ) -> Option<(String, Vec<CValue>, Bitvector32Term)> {
        self.counted_populations
            .iter()
            .find(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments.len() == arguments.len()
                    && population
                        .arguments
                        .iter()
                        .zip(arguments)
                        .all(|(left, right)| {
                            c_values_proven_equal_for_memory_resolution(left, right, assumptions)
                        })
            })
            .map(|population| {
                (
                    population.name.clone(),
                    population.arguments.clone(),
                    population.count.clone(),
                )
            })
    }

    pub fn counted_population_sum(
        &self,
        name: &str,
        arguments: &[Option<CValue>],
        assumptions: &PureFactContext,
    ) -> Bitvector32Term {
        self.counted_populations
            .iter()
            .filter(|population| {
                !population.family_observation_marker
                    && population.name == name
                    && population.arguments.len() == arguments.len()
                    && population
                        .arguments
                        .iter()
                        .zip(arguments)
                        .all(|(actual, expected)| {
                            expected.as_ref().is_none_or(|expected| {
                                c_values_proven_equal_for_memory_resolution(
                                    actual,
                                    expected,
                                    assumptions,
                                )
                            })
                        })
            })
            .fold(Bitvector32Term::Constant(0), |total, population| {
                Bitvector32Term::add(total, population.count.clone())
            })
    }

    pub fn without_counted_population(mut self, name: &str, arguments: &[CValue]) -> Self {
        std::sync::Arc::make_mut(&mut self.counted_populations).retain(|population| {
            population.family_observation_marker
                || population.name != name
                || population.arguments != arguments
        });
        self
    }

    pub fn counted_populations(&self) -> impl Iterator<Item = &CCountedPopulation> {
        self.counted_populations
            .iter()
            .filter(|population| !population.family_observation_marker)
    }

    pub fn with_observed_population_family(mut self, name: impl Into<String>) -> Self {
        let name = name.into();
        if !self.observes_population_family(&name) {
            std::sync::Arc::make_mut(&mut self.counted_populations).push(CCountedPopulation {
                name,
                arguments: Vec::new(),
                count: Bitvector32Term::Constant(0),
                family_observation_marker: true,
            });
        }
        self
    }

    pub fn observes_population_family(&self, name: &str) -> bool {
        self.counted_populations
            .iter()
            .any(|population| population.family_observation_marker && population.name == name)
    }

    /// The logical resource-state component used to index predicate facts.
    ///
    /// Predicate memory arguments retain their existing, explicit snapshot
    /// representation. Keeping memory and locals out of this value prevents
    /// an unrelated C step from changing the identity of a predicate merely
    /// because the predicate language can also observe resource counts.
    pub fn resource_state_snapshot(&self) -> Self {
        let observed_families = self
            .counted_populations
            .iter()
            .filter(|population| population.family_observation_marker)
            .map(|population| population.name.as_str())
            .collect::<BTreeSet<_>>();
        let counted_populations = self
            .counted_populations
            .iter()
            .filter(|population| {
                population.family_observation_marker
                    || observed_families.contains(population.name.as_str())
            })
            .cloned()
            .collect();
        Self {
            counted_populations: std::sync::Arc::new(counted_populations),
            ..Self::new()
        }
    }
}
