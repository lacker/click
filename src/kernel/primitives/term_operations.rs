use super::*;

fn checked_signed_divide_const(left: u32, right: u32) -> Option<u32> {
    let left = left as i32;
    let right = right as i32;
    if right == 0 || (left == i32::MIN && right == -1) {
        None
    } else {
        Some((left / right) as u32)
    }
}

fn checked_signed_remainder_const(left: u32, right: u32) -> Option<u32> {
    let left = left as i32;
    let right = right as i32;
    if right == 0 || (left == i32::MIN && right == -1) {
        None
    } else {
        Some((left % right) as u32)
    }
}

fn checked_shift_count_const(count: u32) -> Option<u32> {
    let count = count as i32;
    (0..32).contains(&count).then_some(count as u32)
}

fn checked_signed_shift_left_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    let left = left as i32;
    if left < 0 {
        return None;
    }
    let shifted = (left as i64) << count;
    (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
}

fn checked_arithmetic_shift_right_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    Some(((left as i32) >> count) as u32)
}

fn signed_shift_left_overflows_const(left: u32, right: u32) -> Option<bool> {
    let count = checked_shift_count_const(right)?;
    let left = left as i32;
    if left < 0 {
        return Some(false);
    }
    Some(((left as i64) << count) > i64::from(i32::MAX))
}

impl Bitvector32Term {
    pub fn var(var: Variable) -> Self {
        Self::Variable(var)
    }

    pub fn constant(value: u32) -> Self {
        Self::Constant(value)
    }

    pub(crate) fn as_const(&self) -> Option<u32> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) | Self::MemoryLoad(_, _) | Self::PureFunctionApplication { .. } => {
                None
            }
            Self::Add(left, right) => Some(left.as_const()?.wrapping_add(right.as_const()?)),
            Self::Subtract(left, right) => Some(left.as_const()?.wrapping_sub(right.as_const()?)),
            Self::Multiply(left, right) => Some(left.as_const()?.wrapping_mul(right.as_const()?)),
            Self::Divide(left, right) => {
                checked_signed_divide_const(left.as_const()?, right.as_const()?)
            }
            Self::Remainder(left, right) => {
                checked_signed_remainder_const(left.as_const()?, right.as_const()?)
            }
            Self::ShiftLeft(left, right) => {
                checked_signed_shift_left_const(left.as_const()?, right.as_const()?)
            }
            Self::ArithmeticShiftRight(left, right) => {
                checked_arithmetic_shift_right_const(left.as_const()?, right.as_const()?)
            }
            Self::BitwiseAnd(left, right) => Some(left.as_const()? & right.as_const()?),
            Self::BitwiseOr(left, right) => Some(left.as_const()? | right.as_const()?),
            Self::BitwiseXor(left, right) => Some(left.as_const()? ^ right.as_const()?),
            Self::BitwiseNot(value) => Some(!value.as_const()?),
            Self::If {
                condition,
                then_term,
                else_term,
            } => match condition.as_ref() {
                ConditionTerm::Constant(true) => then_term.as_const(),
                ConditionTerm::Constant(false) => else_term.as_const(),
                _ => None,
            },
            Self::RangeFold { .. } => None,
        }
    }

    pub(in crate::kernel) fn subtract_one_base(&self) -> Option<Self> {
        match self {
            Self::Subtract(left, right) if right.as_ref() == &Self::Constant(1) => {
                Some(left.as_ref().clone())
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn is_subtract_one(&self) -> bool {
        self.subtract_one_base().is_some()
    }

    pub(in crate::kernel) fn add_const_base(&self, value: u32) -> Option<Self> {
        match self {
            Self::Add(left, right) if right.as_ref() == &Self::Constant(value) => {
                Some(left.as_ref().clone())
            }
            Self::Add(left, right) if left.as_ref() == &Self::Constant(value) => {
                Some(right.as_ref().clone())
            }
            _ => None,
        }
    }

    pub(in crate::kernel) fn add_const_parts(&self) -> Option<(Self, u32)> {
        match self {
            Self::Add(left, right) => match (left.as_ref(), right.as_ref()) {
                (base, Self::Constant(value)) => Some((base.clone(), *value)),
                (Self::Constant(value), base) => Some((base.clone(), *value)),
                _ => None,
            },
            _ => None,
        }
    }

    pub(in crate::kernel) fn subtract_const_parts(&self) -> Option<(Self, u32)> {
        match self {
            Self::Subtract(left, right) => match right.as_ref() {
                Self::Constant(value) => Some((left.as_ref().clone(), *value)),
                _ => None,
            },
            _ => None,
        }
    }

    pub(crate) fn add(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                Self::Constant(left.wrapping_add(*right))
            }
            (_, Self::Subtract(base, subtrahend)) if subtrahend.as_ref() == &left => {
                base.as_ref().clone()
            }
            (Self::Subtract(base, subtrahend), _) if subtrahend.as_ref() == &right => {
                base.as_ref().clone()
            }
            (Self::Subtract(zero, subtrahend), Self::Add(base, addend))
                if zero.as_ref() == &Self::Constant(0) && subtrahend == base =>
            {
                addend.as_ref().clone()
            }
            (Self::Subtract(zero, subtrahend), Self::Add(addend, base))
                if zero.as_ref() == &Self::Constant(0) && subtrahend == base =>
            {
                addend.as_ref().clone()
            }
            (Self::Add(base, addend), Self::Subtract(zero, subtrahend))
                if zero.as_ref() == &Self::Constant(0) && base == subtrahend =>
            {
                addend.as_ref().clone()
            }
            (Self::Add(addend, base), Self::Subtract(zero, subtrahend))
                if zero.as_ref() == &Self::Constant(0) && base == subtrahend =>
            {
                addend.as_ref().clone()
            }
            (_, Self::Constant(0)) => left,
            (Self::Constant(0), _) => right,
            _ => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn subtract(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                Self::Constant(left.wrapping_sub(*right))
            }
            (_, Self::Constant(0)) => left,
            _ if left == right => Self::Constant(0),
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_base == right_base =>
            {
                Self::subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_base == right_addend =>
            {
                Self::subtract(left_addend.as_ref().clone(), right_base.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_addend == right_base =>
            {
                Self::subtract(left_base.as_ref().clone(), right_addend.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), Self::Add(right_base, right_addend))
                if left_addend == right_addend =>
            {
                Self::subtract(left_base.as_ref().clone(), right_base.as_ref().clone())
            }
            (Self::Add(left_base, left_addend), _) if left_base.as_ref() == &right => {
                left_addend.as_ref().clone()
            }
            (Self::Add(left_base, left_addend), _) if left_addend.as_ref() == &right => {
                left_base.as_ref().clone()
            }
            (_, Self::Add(right_base, right_addend)) if &left == right_base.as_ref() => {
                Self::subtract(Self::Constant(0), right_addend.as_ref().clone())
            }
            (_, Self::Add(right_base, right_addend)) if &left == right_addend.as_ref() => {
                Self::subtract(Self::Constant(0), right_base.as_ref().clone())
            }
            _ => Self::Subtract(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn multiply(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                Self::Constant(left.wrapping_mul(*right))
            }
            (_, Self::Constant(1)) => left,
            (Self::Constant(1), _) => right,
            (_, Self::Constant(0)) | (Self::Constant(0), _) => Self::Constant(0),
            _ => Self::Multiply(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn divide(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_signed_divide_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::Divide(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            (_, Self::Constant(1)) => left,
            _ => Self::Divide(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn remainder(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_signed_remainder_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::Remainder(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            _ => Self::Remainder(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn shift_left(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_signed_shift_left_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::ShiftLeft(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            _ => Self::ShiftLeft(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn arithmetic_shift_right(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_arithmetic_shift_right_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::ArithmeticShiftRight(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            (_, Self::Constant(0)) => left,
            _ => Self::ArithmeticShiftRight(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn bitwise_and(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => Self::Constant(*left & *right),
            (_, Self::Constant(u32::MAX)) => left,
            (Self::Constant(u32::MAX), _) => right,
            (_, Self::Constant(0)) | (Self::Constant(0), _) => Self::Constant(0),
            _ if left == right => left,
            _ => Self::BitwiseAnd(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn bitwise_or(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => Self::Constant(*left | *right),
            (_, Self::Constant(0)) => left,
            (Self::Constant(0), _) => right,
            (_, Self::Constant(u32::MAX)) | (Self::Constant(u32::MAX), _) => {
                Self::Constant(u32::MAX)
            }
            _ if left == right => left,
            _ => Self::BitwiseOr(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn bitwise_xor(left: Self, right: Self) -> Self {
        fn flatten(term: Bitvector32Term, constant: &mut u32, terms: &mut Vec<Bitvector32Term>) {
            match term {
                Bitvector32Term::Constant(value) => *constant ^= value,
                Bitvector32Term::BitwiseXor(left, right) => {
                    flatten(*left, constant, terms);
                    flatten(*right, constant, terms);
                }
                term => terms.push(term),
            }
        }

        let mut constant = 0;
        let mut terms = Vec::new();
        flatten(left, &mut constant, &mut terms);
        flatten(right, &mut constant, &mut terms);
        terms.sort();

        let mut normalized = Vec::new();
        let mut index = 0;
        while index < terms.len() {
            let mut end = index + 1;
            while end < terms.len() && terms[end] == terms[index] {
                end += 1;
            }
            if (end - index) % 2 == 1 {
                normalized.push(terms[index].clone());
            }
            index = end;
        }
        if constant != 0 {
            normalized.push(Self::Constant(constant));
            normalized.sort();
        }

        normalized
            .into_iter()
            .reduce(|left, right| Self::BitwiseXor(Box::new(left), Box::new(right)))
            .unwrap_or(Self::Constant(0))
    }

    pub(in crate::kernel) fn bitwise_not(value: Self) -> Self {
        match value {
            Self::Constant(value) => Self::Constant(!value),
            Self::BitwiseNot(inner) => *inner,
            value => Self::BitwiseNot(Box::new(value)),
        }
    }

    pub fn if_then_else(condition: ConditionTerm, then_term: Self, else_term: Self) -> Self {
        match condition {
            ConditionTerm::Constant(true) => then_term,
            ConditionTerm::Constant(false) => else_term,
            _ if then_term == else_term => then_term,
            condition => Self::If {
                condition: Box::new(condition),
                then_term: Box::new(then_term),
                else_term: Box::new(else_term),
            },
        }
    }

    pub fn range_fold(
        start: Self,
        end: Self,
        initial: Self,
        accumulator: Variable,
        item: Variable,
        body: Self,
    ) -> Self {
        if start == end {
            return initial;
        }

        if Self::add(start.clone(), Self::Constant(1)) == end {
            return instantiate_range_fold_step(&body, accumulator, &initial, item, &start);
        }

        if let (Some(start_value), Some(end_value)) = (
            signed_bitvector_constant(&start),
            signed_bitvector_constant(&end),
        ) {
            let length = end_value - start_value;
            if length <= 0 {
                return initial;
            }
            if length <= RANGE_FOLD_CONCRETE_UNROLL_LIMIT {
                let mut value = initial;
                for index in start_value..end_value {
                    value = instantiate_range_fold_step(
                        &body,
                        accumulator,
                        &value,
                        item,
                        &signed_i64_bitvector_constant(index),
                    );
                }
                return value;
            }
        }

        Self::RangeFold {
            start: Box::new(start),
            end: Box::new(end),
            initial: Box::new(initial),
            accumulator,
            item,
            body: Box::new(body),
        }
    }
}

impl PointerOffsetTerm {
    pub fn constant(value: i64) -> Self {
        Self::Constant(value)
    }

    pub(in crate::kernel) fn as_const(&self) -> Option<i64> {
        match self {
            Self::Constant(value) => Some(*value),
            Self::Variable(_) => None,
            Self::Add(left, right) => left.as_const()?.checked_add(right.as_const()?),
            Self::Int32Scaled { value, byte_width } => {
                let value = value.as_const()? as i32 as i64;
                value.checked_mul(*byte_width)
            }
        }
    }

    pub(crate) fn add(left: Self, right: Self) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left + right),
            (Some(0), _) => right,
            (_, Some(0)) => left,
            _ => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn scale_int32(value: Bitvector32Term, byte_width: i64) -> Self {
        match value.as_const() {
            Some(value) => Self::Constant((value as i32 as i64) * byte_width),
            None => Self::Int32Scaled {
                value: Box::new(value),
                byte_width,
            },
        }
    }
}

impl ConditionTerm {
    pub(in crate::kernel) fn signed_less_than(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) < (right as i32)),
            _ => Self::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn signed_less_equal(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) <= (right as i32)),
            _ => Self::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn signed_greater_than(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) > (right as i32)),
            _ => Self::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn signed_greater_equal(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant((left as i32) >= (right as i32)),
            _ => Self::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::Bitvector32Equal(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn signed_add_overflows(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_add(right as i32).1)
            }
            _ => Self::Bitvector32SignedAddOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn signed_subtract_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_sub(right as i32).1)
            }
            _ => Self::Bitvector32SignedSubtractOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn signed_multiply_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant((left as i32).overflowing_mul(right as i32).1)
            }
            _ => Self::Bitvector32SignedMultiplyOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn signed_divide_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(left == i32::MIN as u32 && right == (-1i32) as u32)
            }
            _ => Self::Bitvector32SignedDivideOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn signed_shift_left_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(signed_shift_left_overflows_const(left, right).unwrap_or(false))
            }
            _ => Self::Bitvector32SignedShiftLeftOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(in crate::kernel) fn pointer_offset_equal(
        left: PointerOffsetTerm,
        right: PointerOffsetTerm,
    ) -> Self {
        match (left.as_const(), right.as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::PointerOffsetEqual(Box::new(left), Box::new(right)),
        }
    }

    pub fn pointer_equal(left: Pointer, right: Pointer) -> Self {
        if left == right {
            Self::Constant(true)
        } else if left.blocks_proven_distinct(&right) {
            Self::Constant(false)
        } else if left.block == right.block {
            Self::pointer_offset_equal(left.offset, right.offset)
        } else {
            Self::PointerEqual(Box::new(left), Box::new(right))
        }
    }
}

impl CType {
    pub(in crate::kernel) fn accepts(self, value: &CValue) -> bool {
        matches!(
            (self, value),
            (Self::Void, CValue::Void)
                | (Self::Int32, CValue::Int32(_))
                | (Self::UInt8, CValue::UInt8(_))
                | (Self::Int32Pointer, CValue::Pointer(_))
                | (Self::UInt8Pointer, CValue::Pointer(_))
        )
    }

    pub fn byte_width(self) -> u32 {
        match self {
            Self::Void => 0,
            Self::Int32 => 4,
            Self::UInt8 => 1,
            Self::Int32Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt8Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int32Array(length) => length.saturating_mul(4),
            Self::UInt8Array(length) => length,
        }
    }

    pub fn pointee_type(self) -> Option<Self> {
        match self {
            Self::Int32Pointer => Some(Self::Int32),
            Self::UInt8Pointer => Some(Self::UInt8),
            _ => None,
        }
    }
}

impl CValue {
    pub(in crate::kernel) fn c_type(&self) -> CType {
        match self {
            Self::Void => CType::Void,
            Self::Int32(_) => CType::Int32,
            Self::UInt8(_) => CType::UInt8,
            Self::Pointer(_) => CType::Int32Pointer,
        }
    }

    pub(in crate::kernel) fn byte_width(&self) -> u32 {
        match self {
            Self::Void => 0,
            Self::Int32(_) => 4,
            Self::UInt8(_) => 1,
            Self::Pointer(_) => C_POINTER_BYTE_WIDTH,
        }
    }
}

impl CLValue {
    pub(in crate::kernel) fn local(name: impl Into<String>, value_type: CType) -> Self {
        Self {
            storage: CLValueStorage::Local { name: name.into() },
            value_type,
        }
    }

    pub(in crate::kernel) fn memory(pointer: Pointer, value_type: CType) -> Self {
        Self {
            storage: CLValueStorage::Memory { pointer },
            value_type,
        }
    }

    pub fn value_type(&self) -> CType {
        self.value_type
    }

    pub(in crate::kernel) fn pointer(&self, state: &CState) -> Option<Pointer> {
        match &self.storage {
            CLValueStorage::Local { name } => {
                let pointer = CMemory::local_pointer(name);
                state.memory.has_block(&pointer.block).then_some(pointer)
            }
            CLValueStorage::Memory { pointer } => Some(pointer.clone()),
        }
    }
}

impl Pointer {
    pub(crate) fn null() -> Self {
        Self {
            block: "null".into(),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn symbolic(variable: Variable) -> Self {
        Self {
            block: PointerBlock::Symbolic(variable),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(in crate::kernel) fn has_symbolic_block(&self) -> bool {
        matches!(
            self.block,
            PointerBlock::ExternalArgument | PointerBlock::Symbolic(_)
        )
    }

    pub(in crate::kernel) fn blocks_proven_distinct(&self, other: &Self) -> bool {
        self.block != other.block
            && (matches!(self.block, PointerBlock::Heap(_))
                || matches!(other.block, PointerBlock::Heap(_))
                || matches!(
                    (&self.block, &other.block),
                    (PointerBlock::Concrete(left), PointerBlock::Concrete(right)) if left != right
                ))
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(in crate::kernel) fn offset_by_int32_elements(&self, elements: Bitvector32Term) -> Self {
        self.offset_by_elements(elements, 4)
    }

    pub(crate) fn offset_by_bytes(&self, bytes: u32) -> Self {
        Self {
            block: self.block.clone(),
            offset: PointerOffsetTerm::add(
                self.offset.clone(),
                PointerOffsetTerm::Constant(i64::from(bytes)),
            ),
        }
    }

    pub(in crate::kernel) fn offset_by_elements(
        &self,
        elements: Bitvector32Term,
        byte_width: u32,
    ) -> Self {
        Self {
            block: self.block.clone(),
            offset: PointerOffsetTerm::add(
                self.offset.clone(),
                PointerOffsetTerm::scale_int32(elements, i64::from(byte_width)),
            ),
        }
    }

    pub(crate) fn element_index_from_base(&self, base: &Self) -> Option<Bitvector32Term> {
        if self.block != base.block {
            return None;
        }

        if self.offset == base.offset {
            return Some(Bitvector32Term::Constant(0));
        }

        if base.offset == PointerOffsetTerm::Constant(0) {
            return int32_element_index_from_offset(&self.offset);
        }

        match &self.offset {
            PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
                int32_element_index_from_offset(right)
            }
            PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
                int32_element_index_from_offset(left)
            }
            _ => {
                if let (Some(pointer_index), Some(base_index)) = (
                    int32_element_index_from_offset(&self.offset),
                    int32_element_index_from_offset(&base.offset),
                ) {
                    Some(Bitvector32Term::subtract(pointer_index, base_index))
                } else {
                    None
                }
            }
        }
    }
}
