use super::*;
use std::fmt::Write;

fn memory_havoc_write_set_identity(mutable_ranges: &[CMemoryRange]) -> Vec<String> {
    let mut identity = mutable_ranges
        .iter()
        .map(|range| {
            let mut identity = String::new();
            identity.push_str("range(");
            havoc_pointer_identity(&mut identity, range.base(), 0);
            identity.push_str(", ");
            havoc_bitvector_identity(&mut identity, range.start(), 0);
            identity.push_str(", ");
            havoc_bitvector_identity(&mut identity, range.end(), 0);
            let _ = write!(identity, ", {})", range.element_width());
            identity
        })
        .collect::<Vec<_>>();
    identity.sort();
    identity
}

fn havoc_pointer_identity(identity: &mut String, pointer: &Pointer, depth: usize) {
    if depth >= 64 {
        identity.push_str("depth-limit");
        return;
    }
    let _ = write!(identity, "pointer({:?}, ", pointer.block);
    havoc_pointer_offset_identity(identity, &pointer.offset, depth + 1);
    identity.push(')');
}

fn havoc_pointer_offset_identity(identity: &mut String, offset: &PointerOffsetTerm, depth: usize) {
    if depth >= 64 {
        identity.push_str("depth-limit");
        return;
    }
    match offset {
        PointerOffsetTerm::Constant(value) => {
            let _ = write!(identity, "constant({value})");
        }
        PointerOffsetTerm::Variable(variable) => {
            if let Some((_, pointer)) = crate::kernel::eval::registered_load_for_variable(variable)
            {
                identity.push_str("load(");
                havoc_pointer_identity(identity, &pointer, depth + 1);
                identity.push(')');
            } else {
                let _ = write!(identity, "variable({})", variable.0);
            }
        }
        PointerOffsetTerm::Add(left, right) => {
            identity.push_str("add(");
            havoc_pointer_offset_identity(identity, left, depth + 1);
            identity.push_str(", ");
            havoc_pointer_offset_identity(identity, right, depth + 1);
            identity.push(')');
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            let _ = write!(identity, "scaled(");
            havoc_bitvector_identity(identity, value, depth + 1);
            let _ = write!(identity, ", {byte_width})");
        }
    }
}

fn havoc_bitvector_identity(identity: &mut String, term: &Bitvector32Term, depth: usize) {
    if depth >= 64 {
        identity.push_str("depth-limit");
        return;
    }
    match term {
        Bitvector32Term::Constant(value) => {
            let _ = write!(identity, "constant({value})");
        }
        Bitvector32Term::Variable(variable) => {
            if let Some((_, pointer)) = crate::kernel::eval::registered_load_for_variable(variable)
            {
                identity.push_str("load(");
                havoc_pointer_identity(identity, &pointer, depth + 1);
                identity.push(')');
            } else {
                let _ = write!(identity, "variable({})", variable.0);
            }
        }
        Bitvector32Term::Add(left, right) => {
            havoc_bitvector_binary_identity(identity, "add", left, right, depth)
        }
        Bitvector32Term::Subtract(left, right) => {
            havoc_bitvector_binary_identity(identity, "subtract", left, right, depth)
        }
        Bitvector32Term::Multiply(left, right) => {
            havoc_bitvector_binary_identity(identity, "multiply", left, right, depth)
        }
        Bitvector32Term::Divide(left, right) => {
            havoc_bitvector_binary_identity(identity, "divide", left, right, depth)
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            havoc_bitvector_binary_identity(identity, "unsigned-divide", left, right, depth)
        }
        Bitvector32Term::Remainder(left, right) => {
            havoc_bitvector_binary_identity(identity, "remainder", left, right, depth)
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            havoc_bitvector_binary_identity(identity, "unsigned-remainder", left, right, depth)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            havoc_bitvector_binary_identity(identity, "shift-left", left, right, depth)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            havoc_bitvector_binary_identity(identity, "arithmetic-shift-right", left, right, depth)
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            havoc_bitvector_binary_identity(identity, "logical-shift-right", left, right, depth)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            havoc_bitvector_binary_identity(identity, "bitwise-and", left, right, depth)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            havoc_bitvector_binary_identity(identity, "bitwise-or", left, right, depth)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            havoc_bitvector_binary_identity(identity, "bitwise-xor", left, right, depth)
        }
        Bitvector32Term::BitwiseNot(value) => {
            identity.push_str("bitwise-not(");
            havoc_bitvector_identity(identity, value, depth + 1);
            identity.push(')');
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            identity.push_str("if(");
            havoc_condition_identity(identity, condition, depth + 1);
            identity.push_str(", ");
            havoc_bitvector_identity(identity, then_term, depth + 1);
            identity.push_str(", ");
            havoc_bitvector_identity(identity, else_term, depth + 1);
            identity.push(')');
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            identity.push_str("range-fold(");
            havoc_bitvector_identity(identity, start, depth + 1);
            identity.push_str(", ");
            havoc_bitvector_identity(identity, end, depth + 1);
            identity.push_str(", ");
            havoc_bitvector_identity(identity, initial, depth + 1);
            let _ = write!(identity, ", {}, ", accumulator.0);
            let _ = write!(identity, "{}, ", item.0);
            havoc_bitvector_identity(identity, body, depth + 1);
            identity.push(')');
        }
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            let _ = write!(identity, "pure({name:?}, [");
            for (index, argument) in arguments.iter().enumerate() {
                if index > 0 {
                    identity.push_str(", ");
                }
                havoc_bitvector_identity(identity, argument, depth + 1);
            }
            identity.push_str("])");
        }
        Bitvector32Term::MemoryLoad(_, pointer) => {
            identity.push_str("load(");
            havoc_pointer_identity(identity, pointer, depth + 1);
            identity.push(')');
        }
    }
}

fn havoc_bitvector_binary_identity(
    identity: &mut String,
    name: &str,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    depth: usize,
) {
    identity.push_str(name);
    identity.push('(');
    havoc_bitvector_identity(identity, left, depth + 1);
    identity.push_str(", ");
    havoc_bitvector_identity(identity, right, depth + 1);
    identity.push(')');
}

fn havoc_condition_identity(identity: &mut String, condition: &ConditionTerm, depth: usize) {
    if depth >= 64 {
        identity.push_str("depth-limit");
        return;
    }
    match condition {
        ConditionTerm::Constant(value) => {
            let _ = write!(identity, "constant({value})");
        }
        ConditionTerm::Variable(variable) => {
            let _ = write!(identity, "variable({})", variable.0);
        }
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            havoc_condition_binary_identity(identity, "less-than", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            havoc_condition_binary_identity(identity, "less-equal", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            havoc_condition_binary_identity(identity, "greater-than", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            havoc_condition_binary_identity(identity, "greater-equal", left, right, depth)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            havoc_condition_binary_identity(identity, "equal", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
            havoc_condition_binary_identity(identity, "add-overflows", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => {
            havoc_condition_binary_identity(identity, "subtract-overflows", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => {
            havoc_condition_binary_identity(identity, "multiply-overflows", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => {
            havoc_condition_binary_identity(identity, "divide-overflows", left, right, depth)
        }
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            havoc_condition_binary_identity(identity, "shift-left-overflows", left, right, depth)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            identity.push_str("offset-equal(");
            havoc_pointer_offset_identity(identity, left, depth + 1);
            identity.push_str(", ");
            havoc_pointer_offset_identity(identity, right, depth + 1);
            identity.push(')');
        }
        ConditionTerm::PointerEqual(left, right) => {
            identity.push_str("pointer-equal(");
            havoc_pointer_identity(identity, left, depth + 1);
            identity.push_str(", ");
            havoc_pointer_identity(identity, right, depth + 1);
            identity.push(')');
        }
    }
}

fn havoc_condition_binary_identity(
    identity: &mut String,
    name: &str,
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    depth: usize,
) {
    identity.push_str(name);
    identity.push('(');
    havoc_bitvector_identity(identity, left, depth + 1);
    identity.push_str(", ");
    havoc_bitvector_identity(identity, right, depth + 1);
    identity.push(')');
}

fn memory_havoc_write_set_fingerprint(mutable_ranges: &[CMemoryRange]) -> u32 {
    use std::hash::{Hash, Hasher};

    // This compact marker fingerprint remains form-invariant across proof
    // execution and independent certification. Call havocs supplement it with
    // a lossless structural key below; loop markers retain this shape because
    // their checked write set is already carried by the derivation edge.
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
}

pub(crate) fn resource_context_has_symbolic_int32_range_read(
    resources: &ResourceContext,
    base: &Pointer,
    bytes: &Bitvector32Term,
    assumptions: &PureFactContext,
) -> bool {
    let elements = match bytes {
        Bitvector32Term::Constant(bytes) if bytes % 4 == 0 => Bitvector32Term::Constant(bytes / 4),
        Bitvector32Term::Multiply(left, right) if **right == Bitvector32Term::Constant(4) => {
            left.as_ref().clone()
        }
        Bitvector32Term::Multiply(left, right) if **left == Bitvector32Term::Constant(4) => {
            right.as_ref().clone()
        }
        _ => return false,
    };
    let required = CMemoryRange::new(base.clone(), Bitvector32Term::Constant(0), elements);
    resources.facts().iter().any(|fact| {
        let Some(range) = fact.memory_range() else {
            return false;
        };
        range.element_width() == 4
            && crate::kernel::primitives::resource_algebra::memory_range_covers(
                range,
                &required,
                assumptions,
            )
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
        let name = name.into();
        let slot = self
            .bindings
            .get(&name)
            .map(CLocalBinding::slot)
            .cloned()
            .unwrap_or_else(|| CMemory::local_pointer(&name));
        self.set_typed_at(name, value.retag_pointer(c_type), c_type, slot);
    }

    pub(in crate::kernel) fn set_typed_at(
        &mut self,
        name: impl Into<String>,
        value: CValue,
        c_type: CType,
        slot: Pointer,
    ) {
        self.insert_binding(
            name.into(),
            CLocalBinding::Object {
                value,
                c_type,
                slot,
            },
        );
    }

    pub(in crate::kernel) fn set_uninitialized(&mut self, name: impl Into<String>, c_type: CType) {
        let name = name.into();
        self.set_uninitialized_at(name.clone(), c_type, CMemory::local_pointer(&name));
    }

    pub(in crate::kernel) fn set_uninitialized_at(
        &mut self,
        name: impl Into<String>,
        c_type: CType,
        slot: Pointer,
    ) {
        self.insert_binding(
            name.into(),
            CLocalBinding::UninitializedObject { c_type, slot },
        );
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
        let name = name.into();
        self.set_array_object_at(
            name.clone(),
            element_type,
            length,
            CMemory::local_pointer(&name),
        );
    }

    pub(in crate::kernel) fn set_array_object_at(
        &mut self,
        name: impl Into<String>,
        element_type: CType,
        length: u32,
        slot: Pointer,
    ) {
        self.insert_binding(
            name.into(),
            CLocalBinding::ArrayObject {
                element_type,
                length,
                slot,
            },
        );
    }

    pub(in crate::kernel) fn set_aggregate_object_at(
        &mut self,
        name: impl Into<String>,
        layout: CAggregateLayout,
        slot: Pointer,
    ) {
        self.insert_binding(name.into(), CLocalBinding::AggregateObject { layout, slot });
    }

    pub fn get(&self, name: &str) -> Option<&CValue> {
        match self.bindings.get(name) {
            Some(CLocalBinding::Object { value, .. }) => Some(value),
            Some(CLocalBinding::UninitializedObject { .. })
            | Some(CLocalBinding::ArrayObject { .. })
            | Some(CLocalBinding::AggregateObject { .. })
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
                CLocalBinding::UninitializedObject { .. }
                | CLocalBinding::ArrayObject { .. }
                | CLocalBinding::AggregateObject { .. } => None,
            })
    }

    pub fn aggregate_object_values(
        &self,
    ) -> impl Iterator<Item = (&str, &CAggregateLayout, &Pointer)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::AggregateObject { layout, slot } => {
                    Some((name.as_str(), layout, slot))
                }
                CLocalBinding::Object { .. }
                | CLocalBinding::UninitializedObject { .. }
                | CLocalBinding::ArrayObject { .. } => None,
            })
    }

    pub fn array_object_values(&self) -> impl Iterator<Item = (&str, CValue, CType)> + '_ {
        self.bindings
            .iter()
            .filter_map(|(name, binding)| match binding {
                CLocalBinding::ArrayObject {
                    element_type, slot, ..
                } => Some((
                    name.as_str(),
                    CValue::typed_pointer(
                        slot.clone(),
                        element_type
                            .pointer_to()
                            .expect("array element type must have a pointer type"),
                    ),
                    *element_type,
                )),
                CLocalBinding::Object { .. }
                | CLocalBinding::UninitializedObject { .. }
                | CLocalBinding::AggregateObject { .. } => None,
            })
    }

    pub(in crate::kernel) fn object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            None => None,
            Some(CLocalBinding::AggregateObject { .. }) => None,
        }
    }

    pub(in crate::kernel) fn scalar_object_type(&self, name: &str) -> Option<CType> {
        match self.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::UninitializedObject { c_type, .. }) => Some(*c_type),
            Some(CLocalBinding::ArrayObject { .. })
            | Some(CLocalBinding::AggregateObject { .. })
            | None => None,
        }
    }

    pub(in crate::kernel) fn binding(&self, name: &str) -> Option<&CLocalBinding> {
        self.bindings.get(name)
    }

    pub(in crate::kernel) fn slot(&self, name: &str) -> Option<&Pointer> {
        self.binding(name).map(CLocalBinding::slot)
    }

    pub(in crate::kernel) fn name_for_slot(&self, pointer: &Pointer) -> Option<&str> {
        self.slots.get(pointer).map(String::as_str)
    }

    pub(in crate::kernel) fn is_array_object(&self, name: &str) -> bool {
        matches!(self.binding(name), Some(CLocalBinding::ArrayObject { .. }))
    }

    pub(in crate::kernel) fn is_aggregate_object(&self, name: &str) -> bool {
        matches!(
            self.binding(name),
            Some(CLocalBinding::AggregateObject { .. })
        )
    }

    pub(in crate::kernel) fn aggregate_layout(&self, name: &str) -> Option<&CAggregateLayout> {
        match self.binding(name) {
            Some(CLocalBinding::AggregateObject { layout, .. }) => Some(layout),
            _ => None,
        }
    }
}

impl CLocalBinding {
    pub(in crate::kernel) fn slot(&self) -> &Pointer {
        match self {
            Self::Object { slot, .. }
            | Self::UninitializedObject { slot, .. }
            | Self::ArrayObject { slot, .. }
            | Self::AggregateObject { slot, .. } => slot,
        }
    }
}

impl CLocalEnvironment {
    fn insert_binding(&mut self, name: String, binding: CLocalBinding) {
        let slot = binding.slot().clone();
        let old_slot = self.bindings.get(&name).map(CLocalBinding::slot).cloned();
        std::sync::Arc::make_mut(&mut self.bindings).insert(name.clone(), binding);
        if let Some(old_slot) = old_slot
            && old_slot != slot
        {
            std::sync::Arc::make_mut(&mut self.slots).remove(&old_slot);
        }
        std::sync::Arc::make_mut(&mut self.slots).insert(slot, name);
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
        // but tests and any future caller may write them through this
        // constructor, so the refusal lives here.
        if block.starts_with("havoc:") || block.starts_with("call-havoc:") {
            std::sync::Arc::make_mut(&mut self.blocks).insert(block, CBlock::new(size));
            return self;
        }
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.clone(), CBlock::new(size));
        record_c_memory_derivation(&self, CMemoryDerivation::BlockDeclared { base, block });
        self
    }

    /// Adds a synthetic block without claiming that it was declared by a
    /// program transition. Symbolic aggregate return values use this to make
    /// their known layout available for bounds checks while keeping the
    /// symbolic load identity independent of the caller's memory snapshot.
    pub(in crate::kernel) fn with_block_without_derivation(
        mut self,
        block: impl Into<PointerBlock>,
        size: u32,
    ) -> Self {
        std::sync::Arc::make_mut(&mut self.blocks).insert(block.into(), CBlock::new(size));
        self
    }

    pub(in crate::kernel) fn free_heap_block(
        mut self,
        pointer: &Pointer,
    ) -> Result<Self, CInvalidFree> {
        if self.heap.deallocated_allocations.contains_key(pointer) {
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
        let base = Some(intern_c_memory_ref(&self));
        if pointer.block != PointerBlock::ExternalArgument {
            std::sync::Arc::make_mut(&mut self.blocks).remove(&pointer.block);
        }
        std::sync::Arc::make_mut(&mut self.heap)
            .deallocated_allocations
            .insert(pointer.clone(), bytes.clone());
        std::sync::Arc::make_mut(&mut self.heap)
            .uninitialized_allocations
            .remove(pointer);
        std::sync::Arc::make_mut(&mut self.heap)
            .zeroed_allocations
            .remove(pointer);
        std::sync::Arc::make_mut(&mut self.heap)
            .zeroed_prefix_allocations
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

    pub(in crate::kernel) fn is_uninitialized_heap_address(
        &self,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.heap
            .uninitialized_allocations
            .iter()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
            || self
                .heap
                .zeroed_prefix_allocations
                .iter()
                .any(|(base, prefix)| {
                    let Some(offset) = pointer.offset.as_const() else {
                        return false;
                    };
                    let Ok(offset) = u32::try_from(offset) else {
                        return false;
                    };
                    let Some(end) = offset.checked_add(byte_width) else {
                        return false;
                    };
                    heap_allocation_may_contain_pointer(base, pointer)
                        && prefix.as_const().is_some_and(|prefix| end > prefix)
                })
    }

    pub(in crate::kernel) fn is_zeroed_heap_address(
        &self,
        pointer: &Pointer,
        byte_width: u32,
    ) -> bool {
        self.heap
            .zeroed_allocations
            .iter()
            .any(|base| heap_allocation_may_contain_pointer(base, pointer))
            || self
                .heap
                .zeroed_prefix_allocations
                .iter()
                .any(|(base, prefix)| {
                    let Some(offset) = pointer.offset.as_const() else {
                        return false;
                    };
                    let Ok(offset) = u32::try_from(offset) else {
                        return false;
                    };
                    let Some(end) = offset.checked_add(byte_width) else {
                        return false;
                    };
                    heap_allocation_may_contain_pointer(base, pointer)
                        && prefix.as_const().is_some_and(|prefix| end <= prefix)
                })
    }

    pub(in crate::kernel) fn is_deallocated_heap_address(&self, pointer: &Pointer) -> bool {
        self.heap
            .deallocated_allocations
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
        if bytes.as_const() == Some(0) || self.heap.deallocated_allocations.contains_key(&base) {
            return None;
        }
        match self.heap.live_allocations.get(&base) {
            Some(existing) if existing != &bytes => None,
            Some(_) => Some(self),
            None => {
                let prior = Some(intern_c_memory_ref(&self));
                std::sync::Arc::make_mut(&mut self.heap)
                    .live_allocations
                    .insert(base, bytes);
                if let Some(prior) = prior {
                    record_c_memory_derivation(
                        &self,
                        CMemoryDerivation::ContractAllocationClaimsChanged { base: prior },
                    );
                }
                Some(self)
            }
        }
    }

    /// Removes an input allocation claim at an opaque contract boundary.
    ///
    /// The consumed ownership occurrence is gone regardless of whether the
    /// produced occurrence later names the same pointer value. Unlike a C
    /// `free`, this abstraction does not assert deallocation or erase bytes:
    /// the contract may describe continuity, replacement, or either. Return
    /// resources install the sole post-call allocation claim afterwards.
    pub(in crate::kernel) fn retire_contract_heap_allocation_claim(
        mut self,
        base: &Pointer,
    ) -> Self {
        let prior = Some(intern_c_memory_ref(&self));
        let removed_live = std::sync::Arc::make_mut(&mut self.heap)
            .live_allocations
            .remove(base);
        let removed_uninitialized = std::sync::Arc::make_mut(&mut self.heap)
            .uninitialized_allocations
            .remove(base);
        let removed_zeroed_prefix = std::sync::Arc::make_mut(&mut self.heap)
            .zeroed_prefix_allocations
            .remove(base)
            .is_some();
        if (removed_live.is_some() || removed_uninitialized || removed_zeroed_prefix)
            && prior.is_some()
        {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::ContractAllocationClaimsChanged {
                    base: prior.expect("checked above"),
                },
            );
        }
        self
    }

    pub(in crate::kernel) fn with_pending_heap_allocation(
        mut self,
        base: Pointer,
        bytes: Bitvector32Term,
        zeroed: bool,
    ) -> Self {
        let prior = Some(intern_c_memory_ref(&self));
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .insert(base.clone(), bytes.clone());
        if zeroed {
            std::sync::Arc::make_mut(&mut self.heap)
                .zeroed_pending_allocations
                .insert(base.clone());
        }
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

    pub(in crate::kernel) fn with_pending_heap_reallocation(
        mut self,
        base: Pointer,
        old_pointer: Pointer,
        old_bytes: Bitvector32Term,
        zeroed_prefix: Option<Bitvector32Term>,
        copied_cells: Vec<(PointerOffsetTerm, CValue)>,
    ) -> Self {
        std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .insert(
                base,
                CPendingReallocation {
                    old_pointer,
                    old_bytes,
                    zeroed_prefix,
                    copied_cells,
                },
            );
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
                .deallocated_allocations
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
        let prior = Some(intern_c_memory_ref(&self));
        let bytes = std::sync::Arc::make_mut(&mut self.heap)
            .pending_allocations
            .remove(base)?;
        let zeroed = std::sync::Arc::make_mut(&mut self.heap)
            .zeroed_pending_allocations
            .remove(base);
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
            if zeroed {
                std::sync::Arc::make_mut(&mut self.heap)
                    .zeroed_allocations
                    .insert(resolved_base.clone());
            } else {
                std::sync::Arc::make_mut(&mut self.heap)
                    .uninitialized_allocations
                    .insert(resolved_base.clone());
            }
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

    pub(in crate::kernel) fn resolve_pending_heap_reallocation(
        mut self,
        base: &Pointer,
        succeeds: bool,
    ) -> Option<(Self, Bitvector32Term, Pointer, CPendingReallocation)> {
        let pending = std::sync::Arc::make_mut(&mut self.heap)
            .pending_reallocations
            .remove(base)?;
        let (mut memory, bytes, resolved_base) = if succeeds {
            self = self.free_heap_block(&pending.old_pointer).ok()?;
            self.resolve_pending_heap_allocation(base, true)?
        } else {
            self.resolve_pending_heap_allocation(base, false)?
        };
        if succeeds {
            if let Some(zeroed_prefix) = &pending.zeroed_prefix {
                std::sync::Arc::make_mut(&mut memory.heap)
                    .uninitialized_allocations
                    .remove(&resolved_base);
                if zeroed_prefix
                    .as_const()
                    .zip(bytes.as_const())
                    .is_some_and(|(prefix, bytes)| prefix == bytes)
                {
                    std::sync::Arc::make_mut(&mut memory.heap)
                        .zeroed_allocations
                        .insert(resolved_base.clone());
                } else {
                    std::sync::Arc::make_mut(&mut memory.heap)
                        .zeroed_prefix_allocations
                        .insert(resolved_base.clone(), zeroed_prefix.clone());
                }
            }
            for (offset, value) in &pending.copied_cells {
                memory = memory.store(
                    Pointer {
                        block: resolved_base.block.clone(),
                        offset: offset.clone(),
                    },
                    value.clone(),
                );
            }
        }
        Some((memory, bytes, resolved_base, pending))
    }

    pub(in crate::kernel) fn with_loop_memory_havoc(
        mut self,
        variable: Variable,
        preserved_blocks: &BTreeSet<PointerBlock>,
        mutable_ranges: Option<&[CMemoryRange]>,
    ) -> Self {
        // A loop body that may write memory can clobber, through some
        // pointer, any cell it can reach. Drop concrete cells outside the
        // preserved (scalar stack local) blocks so loop-head and post-loop
        // reads do not observe stale pre-loop values. A checked footprint is
        // retained on the derivation edge for disjoint-load transport; the
        // marker block still distinguishes this havoc from ordinary memory.
        let base = Some(intern_c_memory_ref(&self));
        std::sync::Arc::make_mut(&mut self.cells)
            .retain(|pointer, _| preserved_blocks.contains(&pointer.block));
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("havoc:{}", variable.0).into(),
            CBlock::new(mutable_ranges.map_or(0, memory_havoc_write_set_fingerprint)),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::LoopHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.map(|ranges| ranges.to_vec()),
                },
            );
        }
        self
    }

    /// Forgets branch-local cell values and constructs the conservative heap
    /// state exported by an interface join. A branch may retire an allocation
    /// while its sibling keeps it live; the join must retain the potential
    /// live allocation so a guarded resource can decide whether the
    /// continuation may use it. Tombstones are retained only when every arm
    /// agrees that the allocation is retired.
    ///
    /// This is deliberately separate from loop havoc. The joined heap is the
    /// union of potential live allocations, so making the transition look like
    /// a loop havoc would record a false memory-DAG derivation. The resulting
    /// snapshot is a provenance barrier instead: no load from before the
    /// branch may be transported across it without explicit interface facts.
    pub(in crate::kernel) fn with_interface_memory_havoc(
        mut self,
        variable: Variable,
        preserved_blocks: &BTreeSet<PointerBlock>,
        sibling_memories: &[&CMemory],
    ) -> Result<Self, String> {
        let Some(first) = sibling_memories.first() else {
            return Err("an interface memory join has no sibling states".to_string());
        };

        let mut blocks = BTreeMap::new();
        for memory in sibling_memories {
            for (block, contents) in memory.blocks.iter() {
                if let Some(existing) = blocks.insert(block.clone(), contents.clone())
                    && existing != *contents
                {
                    return Err(format!(
                        "interface arms disagree on the size of memory block {block:?}"
                    ));
                }
            }
        }

        let mut live_allocations = BTreeMap::new();
        for memory in sibling_memories {
            for (base, bytes) in &memory.heap.live_allocations {
                if let Some(existing) = live_allocations.insert(base.clone(), bytes.clone())
                    && existing != *bytes
                {
                    return Err(format!(
                        "interface arms disagree on the size of heap allocation {base:?}"
                    ));
                }
            }
        }

        let mut deallocated_allocations = first.heap.deallocated_allocations.clone();
        deallocated_allocations.retain(|base, bytes| {
            !live_allocations.contains_key(base)
                && sibling_memories
                    .iter()
                    .all(|memory| memory.heap.deallocated_allocations.get(base) == Some(bytes))
        });

        let pending_allocations = first.heap.pending_allocations.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.pending_allocations != pending_allocations)
        {
            return Err("interface arms disagree on pending heap allocations".to_string());
        }
        let pending_reallocations = first.heap.pending_reallocations.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.pending_reallocations != pending_reallocations)
        {
            return Err("interface arms disagree on pending heap reallocations".to_string());
        }

        let mut uninitialized_allocations = first.heap.uninitialized_allocations.clone();
        for memory in sibling_memories {
            uninitialized_allocations.extend(memory.heap.uninitialized_allocations.iter().cloned());
        }

        // A zero marker is a value guarantee, so it is retained only when
        // every arm provides it. (The uninitialized marker above is instead
        // unioned because a possibly-uninitialized read must remain unsafe.)
        let mut zeroed_allocations = first.heap.zeroed_allocations.clone();
        zeroed_allocations.retain(|base| {
            sibling_memories
                .iter()
                .all(|memory| memory.heap.zeroed_allocations.contains(base))
        });
        let mut zeroed_prefix_allocations = BTreeMap::new();
        for base in live_allocations.keys() {
            let prefixes = sibling_memories
                .iter()
                .map(|memory| {
                    if memory.heap.zeroed_allocations.contains(base) {
                        memory.heap.live_allocations.get(base).cloned()
                    } else {
                        memory.heap.zeroed_prefix_allocations.get(base).cloned()
                    }
                })
                .collect::<Option<Vec<_>>>();
            let Some(prefixes) = prefixes else {
                continue;
            };
            let Some(prefixes) = prefixes
                .iter()
                .map(Bitvector32Term::as_const)
                .collect::<Option<Vec<_>>>()
            else {
                continue;
            };
            if sibling_memories
                .iter()
                .any(|memory| !memory.heap.zeroed_allocations.contains(base))
            {
                zeroed_allocations.remove(base);
                zeroed_prefix_allocations.insert(
                    base.clone(),
                    Bitvector32Term::Constant(
                        prefixes.into_iter().min().expect("nonempty interface arms"),
                    ),
                );
            }
        }
        let zeroed_pending_allocations = first.heap.zeroed_pending_allocations.clone();
        if sibling_memories
            .iter()
            .any(|memory| memory.heap.zeroed_pending_allocations != zeroed_pending_allocations)
        {
            return Err("interface arms disagree on zeroed pending heap allocations".to_string());
        }

        std::sync::Arc::make_mut(&mut self.cells)
            .retain(|pointer, _| preserved_blocks.contains(&pointer.block));
        blocks.insert(format!("havoc:{}", variable.0).into(), CBlock::new(0));
        self.blocks = std::sync::Arc::new(blocks);
        self.heap = std::sync::Arc::new(CHeapMemory {
            live_allocations,
            deallocated_allocations,
            pending_allocations,
            uninitialized_allocations,
            zeroed_allocations,
            zeroed_prefix_allocations,
            zeroed_pending_allocations,
            pending_reallocations,
        });
        Ok(self)
    }

    pub(in crate::kernel) fn with_call_memory_havoc(
        mut self,
        variable: Variable,
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
    ) -> Self {
        let base = Some(intern_c_memory_ref(&self));
        std::sync::Arc::make_mut(&mut self.cells).retain(|pointer, _| {
            pointer.block.starts_with("local:")
                || assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("call-havoc:{}", variable.0).into(),
            CBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges)),
        );
        // Keep the legacy marker's semantic shape and add a collision-free
        // structural key for the checked write set. This key is intentionally
        // not named as a havoc marker: canonical load snapshots must continue
        // to treat the call-havoc edge as the only global memory barrier.
        let identity = memory_havoc_write_set_identity(mutable_ranges);
        std::sync::Arc::make_mut(&mut self.blocks).insert(
            format!("call-write-set:{}:{}", variable.0, identity.join("|")).into(),
            CBlock::new(0),
        );
        if let Some(base) = base {
            record_c_memory_derivation(
                &self,
                CMemoryDerivation::CallHavoc {
                    base,
                    variable,
                    mutable_ranges: mutable_ranges.to_vec(),
                    context: assumptions.clone(),
                },
            );
        }
        self
    }

    /// Checks that `self` is exactly the cell-and-marker result produced by a
    /// call havoc from `before`. This is deliberately a structural producer
    /// check rather than a second alias approximation: erased cells are
    /// accepted only when the endpoint has the call-havoc shape and the same
    /// conservative retention rule as [`Self::with_call_memory_havoc`].
    pub(in crate::kernel) fn matches_call_memory_havoc_result(
        &self,
        before: &Self,
        mutable_ranges: &[CMemoryRange],
        assumptions: &PureFactContext,
    ) -> bool {
        if self.heap != before.heap || self.blocks.len() != before.blocks.len() + 2 {
            return false;
        }
        if !before
            .blocks
            .iter()
            .all(|(block, value)| self.blocks.get(block) == Some(value))
        {
            return false;
        }
        let added_blocks = self
            .blocks
            .iter()
            .filter(|(block, _)| !before.blocks.contains_key(*block))
            .collect::<Vec<_>>();
        let Some((marker, marker_block)) = added_blocks
            .iter()
            .find(|(block, _)| block.starts_with("call-havoc:"))
        else {
            return false;
        };
        let Some(variable) = marker
            .strip_prefix("call-havoc:")
            .and_then(|variable| variable.parse::<u64>().ok())
        else {
            return false;
        };
        let write_set_marker: PointerBlock = format!(
            "call-write-set:{variable}:{}",
            memory_havoc_write_set_identity(mutable_ranges).join("|")
        )
        .into();
        if added_blocks.len() != 2
            || **marker_block != CBlock::new(memory_havoc_write_set_fingerprint(mutable_ranges))
            || self.blocks.get(&write_set_marker) != Some(&CBlock::new(0))
        {
            return false;
        }

        let mut expected_cells = before.cells.as_ref().clone();
        expected_cells.retain(|pointer, _| {
            pointer.block.starts_with("local:")
                || assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        self.cells.as_ref() == &expected_cells
    }

    pub fn store(self, pointer: Pointer, value: CValue) -> Self {
        self.store_with_context(pointer, value, &PureFactContext::new())
    }

    /// Writes one cell, freezing `context` on the store edge: a later load of
    /// another cell of the same base crosses the edge when a strict order
    /// recorded in that context separates the two indexes.
    pub fn store_with_context(
        mut self,
        pointer: Pointer,
        value: CValue,
        context: &PureFactContext,
    ) -> Self {
        let base = intern_c_memory_ref(&self);
        std::sync::Arc::make_mut(&mut self.cells).insert(pointer.clone(), value.clone());
        record_c_memory_derivation(
            &self,
            CMemoryDerivation::Store {
                base,
                pointer,
                value,
                context: context.clone(),
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
        let base = Some(intern_c_memory_ref(self));
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
                // A field cell survives a store into an array it is
                // separated from: separation facts plus range membership
                // decide the cross-base pairs offset reasoning cannot.
                // Only here, per cell per store — not on the general
                // distinctness path, where this scan is too hot.
                || assumptions
                    .pointers_directly_disjoint_by_range(&normalized_cell_pointer, &normalized_pointer)
        });
        // Forgetting nothing is not a transition: the memory is the same
        // snapshot, so a later load keeps resolving through it unchanged
        // instead of stopping at an edge that records no write.
        if memory.cells.len() == self.cells.len() {
            return self.clone();
        }
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

    pub(in crate::kernel) fn frame_local_pointer(frame: u64, name: &str) -> Pointer {
        Pointer {
            block: format!("local:frame:{frame}:{name}").into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn has_block(&self, block: &PointerBlock) -> bool {
        self.blocks.contains_key(block)
    }

    pub(in crate::kernel) fn block_size(&self, block: &PointerBlock) -> Option<&Bitvector32Term> {
        self.blocks.get(block).map(CBlock::size)
    }

    /// Whether some allocation this snapshot has already freed may contain
    /// `pointer`. Freed allocations are few, so this scans them directly.
    pub(in crate::kernel) fn freed_heap_allocation_may_contain(&self, pointer: &Pointer) -> bool {
        self.heap
            .deallocated_allocations
            .keys()
            .any(|allocation| heap_allocation_may_contain_pointer(allocation, pointer))
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

    pub(in crate::kernel) fn symbolic_int16_load(&self, pointer: &Pointer) -> CValue {
        int16(Bitvector32Term::MemoryLoad(
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

    pub(in crate::kernel) fn symbolic_uint16_load(&self, pointer: &Pointer) -> CValue {
        uint16(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_uint32_load(&self, pointer: &Pointer) -> CValue {
        uint32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(self.clone()),
            Box::new(pointer.clone()),
        ))
    }

    pub(in crate::kernel) fn symbolic_pointer_load(
        &self,
        pointer: &Pointer,
        pointee_byte_width: u32,
        value_type: CType,
    ) -> CValue {
        CValue::typed_pointer(
            Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(self.clone()),
                        Box::new(pointer.clone()),
                    ),
                    i64::from(pointee_byte_width),
                ),
            },
            value_type,
        )
    }
}

impl CState {
    pub fn new() -> Self {
        Self::default()
    }

    pub(in crate::kernel) fn next_local_frame(&self) -> u64 {
        self.next_local_frame
    }

    pub(in crate::kernel) fn with_next_local_frame(mut self, next: u64) -> Self {
        self.next_local_frame = next;
        self
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

    /// The values held by memory-resident scalar locals at offset zero.
    /// Resolve names through the local-slot index so framed parameter blocks
    /// are exposed with their source name rather than their internal block id.
    pub fn local_cell_values(&self) -> impl Iterator<Item = (&str, &CValue)> {
        self.memory.cells.iter().filter_map(|(pointer, value)| {
            if pointer.offset != PointerOffsetTerm::Constant(0) {
                return None;
            }
            self.locals.name_for_slot(pointer).map(|name| (name, value))
        })
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
