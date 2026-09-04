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

fn checked_unsigned_divide_const(left: u32, right: u32) -> Option<u32> {
    (right != 0).then_some(left / right)
}

fn checked_unsigned_remainder_const(left: u32, right: u32) -> Option<u32> {
    (right != 0).then_some(left % right)
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

fn checked_logical_shift_right_const(left: u32, right: u32) -> Option<u32> {
    let count = checked_shift_count_const(right)?;
    Some(left >> count)
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
            Self::Variable(_)
            | Self::MemoryLoad(_, _)
            | Self::PureFunctionApplication { .. }
            | Self::Int64Constant(_)
            | Self::UInt64Constant(_)
            | Self::Int64From32(_)
            | Self::Int64FromUInt32(_)
            | Self::UInt64From32(_)
            | Self::UInt64FromInt32(_)
            | Self::UInt64FromInt64(_)
            | Self::Int64Add(_, _)
            | Self::Int64Subtract(_, _)
            | Self::Int64Multiply(_, _)
            | Self::Int64Divide(_, _)
            | Self::Int64Remainder(_, _)
            | Self::Int64ShiftLeft(_, _)
            | Self::Int64ArithmeticShiftRight(_, _)
            | Self::Int64BitwiseAnd(_, _)
            | Self::Int64BitwiseOr(_, _)
            | Self::Int64BitwiseXor(_, _)
            | Self::Int64BitwiseNot(_)
            | Self::UInt64Add(_, _)
            | Self::UInt64Subtract(_, _)
            | Self::UInt64Multiply(_, _)
            | Self::UInt64Divide(_, _)
            | Self::UInt64Remainder(_, _)
            | Self::UInt64ShiftLeft(_, _)
            | Self::UInt64LogicalShiftRight(_, _)
            | Self::UInt64BitwiseAnd(_, _)
            | Self::UInt64BitwiseOr(_, _)
            | Self::UInt64BitwiseXor(_, _)
            | Self::UInt64BitwiseNot(_) => None,
            Self::Add(left, right) => Some(left.as_const()?.wrapping_add(right.as_const()?)),
            Self::Subtract(left, right) => Some(left.as_const()?.wrapping_sub(right.as_const()?)),
            Self::Multiply(left, right) => Some(left.as_const()?.wrapping_mul(right.as_const()?)),
            Self::Divide(left, right) => {
                checked_signed_divide_const(left.as_const()?, right.as_const()?)
            }
            Self::UnsignedDivide(left, right) => {
                checked_unsigned_divide_const(left.as_const()?, right.as_const()?)
            }
            Self::Remainder(left, right) => {
                checked_signed_remainder_const(left.as_const()?, right.as_const()?)
            }
            Self::UnsignedRemainder(left, right) => {
                checked_unsigned_remainder_const(left.as_const()?, right.as_const()?)
            }
            Self::ShiftLeft(left, right) => {
                checked_signed_shift_left_const(left.as_const()?, right.as_const()?)
            }
            Self::ArithmeticShiftRight(left, right) => {
                checked_arithmetic_shift_right_const(left.as_const()?, right.as_const()?)
            }
            Self::LogicalShiftRight(left, right) => {
                checked_logical_shift_right_const(left.as_const()?, right.as_const()?)
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

    pub(crate) fn unsigned_divide(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_unsigned_divide_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::UnsignedDivide(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            (_, Self::Constant(1)) => left,
            _ => Self::UnsignedDivide(Box::new(left), Box::new(right)),
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

    pub(crate) fn unsigned_remainder(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_unsigned_remainder_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::UnsignedRemainder(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            _ => Self::UnsignedRemainder(Box::new(left), Box::new(right)),
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

    pub(in crate::kernel) fn unsigned_shift_left(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_shift_count_const(*right) {
                    Some(count) => Self::Constant(left.wrapping_shl(count)),
                    None => Self::ShiftLeft(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            (_, Self::Constant(0)) => left,
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

    pub(crate) fn logical_shift_right(left: Self, right: Self) -> Self {
        match (&left, &right) {
            (Self::Constant(left), Self::Constant(right)) => {
                match checked_logical_shift_right_const(*left, *right) {
                    Some(value) => Self::Constant(value),
                    None => Self::LogicalShiftRight(
                        Box::new(Self::Constant(*left)),
                        Box::new(Self::Constant(*right)),
                    ),
                }
            }
            (_, Self::Constant(0)) => left,
            _ => Self::LogicalShiftRight(Box::new(left), Box::new(right)),
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
            // A concrete range unrolls step by step: the steps are the
            // range's own length, charged as deterministic work, never cut
            // by a count.
            crate::instrumentation::record_deterministic_work(
                usize::try_from(length).unwrap_or(usize::MAX),
            );
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

// The original term type is retained as the shared arena for both machine
// widths.  These helpers use dedicated constructors and constants for 64-bit
// values, so a 64-bit value can never be mistaken for a wrapped 32-bit one by
// the existing C0 paths.
fn int64_constant(term: &Bitvector32Term) -> Option<i64> {
    match term {
        Bitvector32Term::Int64Constant(value) => Some(*value),
        Bitvector32Term::Int64From32(value) => match value.as_ref() {
            Bitvector32Term::Constant(value) => Some(i64::from(*value as i32)),
            _ => int64_constant(value),
        },
        Bitvector32Term::Int64FromUInt32(value) => match value.as_ref() {
            Bitvector32Term::Constant(value) => Some(i64::from(*value)),
            _ => int64_constant(value),
        },
        Bitvector32Term::Int64Add(left, right) => {
            int64_constant(left)?.checked_add(int64_constant(right)?)
        }
        Bitvector32Term::Int64Subtract(left, right) => {
            int64_constant(left)?.checked_sub(int64_constant(right)?)
        }
        Bitvector32Term::Int64Multiply(left, right) => {
            int64_constant(left)?.checked_mul(int64_constant(right)?)
        }
        Bitvector32Term::Int64Divide(left, right) => {
            let left = int64_constant(left)?;
            let right = int64_constant(right)?;
            (right != 0 && !(left == i64::MIN && right == -1)).then_some(left / right)
        }
        Bitvector32Term::Int64Remainder(left, right) => {
            let left = int64_constant(left)?;
            let right = int64_constant(right)?;
            (right != 0 && !(left == i64::MIN && right == -1)).then_some(left % right)
        }
        Bitvector32Term::Int64ShiftLeft(left, right) => {
            let left = int64_constant(left)?;
            let count = int64_shift_count_constant(right)?;
            (left >= 0 && count < 64)
                .then_some(left.checked_shl(count)?)
                .filter(|value| *value >= 0)
        }
        Bitvector32Term::Int64ArithmeticShiftRight(left, right) => {
            let left = int64_constant(left)?;
            let count = int64_shift_count_constant(right)?;
            (count < 64).then_some(left >> count)
        }
        Bitvector32Term::Int64BitwiseAnd(left, right) => {
            Some(int64_constant(left)? & int64_constant(right)?)
        }
        Bitvector32Term::Int64BitwiseOr(left, right) => {
            Some(int64_constant(left)? | int64_constant(right)?)
        }
        Bitvector32Term::Int64BitwiseXor(left, right) => {
            Some(int64_constant(left)? ^ int64_constant(right)?)
        }
        Bitvector32Term::Int64BitwiseNot(value) => Some(!int64_constant(value)?),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match condition.as_ref() {
            ConditionTerm::Constant(true) => int64_constant(then_term),
            ConditionTerm::Constant(false) => int64_constant(else_term),
            _ => None,
        },
        _ => None,
    }
}

fn uint64_constant(term: &Bitvector32Term) -> Option<u64> {
    match term {
        Bitvector32Term::UInt64Constant(value) => Some(*value),
        Bitvector32Term::UInt64From32(value) => match value.as_ref() {
            Bitvector32Term::Constant(value) => Some(u64::from(*value)),
            _ => uint64_constant(value),
        },
        Bitvector32Term::UInt64FromInt32(value) => match value.as_ref() {
            Bitvector32Term::Constant(value) => Some((*value as i32 as i64) as u64),
            _ => uint64_constant(value),
        },
        Bitvector32Term::UInt64FromInt64(value) => match value.as_ref() {
            Bitvector32Term::Int64Constant(value) => Some(*value as u64),
            _ => uint64_constant(value),
        },
        Bitvector32Term::UInt64Add(left, right) => {
            Some(uint64_constant(left)?.wrapping_add(uint64_constant(right)?))
        }
        Bitvector32Term::UInt64Subtract(left, right) => {
            Some(uint64_constant(left)?.wrapping_sub(uint64_constant(right)?))
        }
        Bitvector32Term::UInt64Multiply(left, right) => {
            Some(uint64_constant(left)?.wrapping_mul(uint64_constant(right)?))
        }
        Bitvector32Term::UInt64Divide(left, right) => {
            let right = uint64_constant(right)?;
            (right != 0).then_some(uint64_constant(left)? / right)
        }
        Bitvector32Term::UInt64Remainder(left, right) => {
            let right = uint64_constant(right)?;
            (right != 0).then_some(uint64_constant(left)? % right)
        }
        Bitvector32Term::UInt64ShiftLeft(left, right) => {
            let count = int64_shift_count_constant(right)?;
            (count < 64).then_some(uint64_constant(left)?.wrapping_shl(count))
        }
        Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            let count = int64_shift_count_constant(right)?;
            (count < 64).then_some(uint64_constant(left)? >> count)
        }
        Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            Some(uint64_constant(left)? & uint64_constant(right)?)
        }
        Bitvector32Term::UInt64BitwiseOr(left, right) => {
            Some(uint64_constant(left)? | uint64_constant(right)?)
        }
        Bitvector32Term::UInt64BitwiseXor(left, right) => {
            Some(uint64_constant(left)? ^ uint64_constant(right)?)
        }
        Bitvector32Term::UInt64BitwiseNot(value) => Some(!uint64_constant(value)?),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match condition.as_ref() {
            ConditionTerm::Constant(true) => uint64_constant(then_term),
            ConditionTerm::Constant(false) => uint64_constant(else_term),
            _ => None,
        },
        _ => None,
    }
}

fn int64_shift_count_constant(term: &Bitvector32Term) -> Option<u32> {
    let value = match term {
        Bitvector32Term::Constant(value) => u64::from(*value),
        Bitvector32Term::Int64Constant(value) if *value >= 0 => *value as u64,
        Bitvector32Term::UInt64Constant(value) => *value,
        _ => return None,
    };
    u32::try_from(value).ok()
}

impl Bitvector32Term {
    pub(crate) fn int64_from_32(value: Self) -> Self {
        match value {
            Self::Constant(value) => Self::Int64Constant(i64::from(value as i32)),
            Self::Int64Constant(_) | Self::Int64From32(_) => value,
            value => Self::Int64From32(Box::new(value)),
        }
    }

    pub(crate) fn uint64_from_32(value: Self) -> Self {
        match value {
            Self::Constant(value) => Self::UInt64Constant(u64::from(value)),
            Self::UInt64Constant(_) | Self::UInt64From32(_) => value,
            value => Self::UInt64From32(Box::new(value)),
        }
    }

    pub(crate) fn int64_from_uint32(value: Self) -> Self {
        match value {
            Self::Constant(value) => Self::Int64Constant(i64::from(value)),
            Self::Int64Constant(_) | Self::Int64FromUInt32(_) => value,
            value => Self::Int64FromUInt32(Box::new(value)),
        }
    }

    pub(crate) fn uint64_from_int32(value: Self) -> Self {
        match value {
            Self::Constant(value) => Self::UInt64Constant((value as i32 as i64) as u64),
            Self::UInt64Constant(_) | Self::UInt64FromInt32(_) => value,
            value => Self::UInt64FromInt32(Box::new(value)),
        }
    }

    pub(crate) fn uint64_from_int64(value: Self) -> Self {
        match value {
            Self::Int64Constant(value) => Self::UInt64Constant(value as u64),
            Self::UInt64Constant(_) | Self::UInt64FromInt64(_) => value,
            value => Self::UInt64FromInt64(Box::new(value)),
        }
    }

    pub(crate) fn int64_as_const(&self) -> Option<i64> {
        int64_constant(self)
    }

    pub(crate) fn uint64_as_const(&self) -> Option<u64> {
        uint64_constant(self)
    }

    fn int64_binary(
        left: Self,
        right: Self,
        operation: impl FnOnce(i64, i64) -> Option<i64>,
        constructor: impl FnOnce(Box<Self>, Box<Self>) -> Self,
    ) -> Self {
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => operation(left, right)
                .map(Self::Int64Constant)
                .unwrap_or_else(|| {
                    constructor(
                        Box::new(Self::Int64Constant(left)),
                        Box::new(Self::Int64Constant(right)),
                    )
                }),
            _ => constructor(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_add(left: Self, right: Self) -> Self {
        Self::int64_binary(left, right, i64::checked_add, Self::Int64Add)
    }

    pub(crate) fn int64_subtract(left: Self, right: Self) -> Self {
        Self::int64_binary(left, right, i64::checked_sub, Self::Int64Subtract)
    }

    pub(crate) fn int64_multiply(left: Self, right: Self) -> Self {
        Self::int64_binary(left, right, i64::checked_mul, Self::Int64Multiply)
    }

    pub(crate) fn int64_divide(left: Self, right: Self) -> Self {
        Self::int64_binary(
            left,
            right,
            |left, right| {
                (right != 0 && !(left == i64::MIN && right == -1)).then_some(left / right)
            },
            Self::Int64Divide,
        )
    }

    pub(crate) fn int64_remainder(left: Self, right: Self) -> Self {
        Self::int64_binary(
            left,
            right,
            |left, right| {
                (right != 0 && !(left == i64::MIN && right == -1)).then_some(left % right)
            },
            Self::Int64Remainder,
        )
    }

    pub(crate) fn int64_shift_left(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if left >= 0 && count < 64 => left
                .checked_shl(count)
                .filter(|value| *value >= 0)
                .map(Self::Int64Constant)
                .unwrap_or_else(|| {
                    Self::Int64ShiftLeft(Box::new(Self::Int64Constant(left)), Box::new(right))
                }),
            _ => Self::Int64ShiftLeft(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_arithmetic_shift_right(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if count < 64 => Self::Int64Constant(left >> count),
            _ => Self::Int64ArithmeticShiftRight(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_bitwise_and(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => Self::Int64Constant(left & right),
            _ => Self::Int64BitwiseAnd(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_bitwise_or(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => Self::Int64Constant(left | right),
            _ => Self::Int64BitwiseOr(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_bitwise_xor(left: Self, right: Self) -> Self {
        match (int64_constant(&left), int64_constant(&right)) {
            (Some(left), Some(right)) => Self::Int64Constant(left ^ right),
            _ => Self::Int64BitwiseXor(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_bitwise_not(value: Self) -> Self {
        match int64_constant(&value) {
            Some(value) => Self::Int64Constant(!value),
            None => Self::Int64BitwiseNot(Box::new(value)),
        }
    }

    fn uint64_binary(
        left: Self,
        right: Self,
        operation: impl FnOnce(u64, u64) -> Option<u64>,
        constructor: impl FnOnce(Box<Self>, Box<Self>) -> Self,
    ) -> Self {
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => operation(left, right)
                .map(Self::UInt64Constant)
                .unwrap_or_else(|| {
                    constructor(
                        Box::new(Self::UInt64Constant(left)),
                        Box::new(Self::UInt64Constant(right)),
                    )
                }),
            _ => constructor(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_add(left: Self, right: Self) -> Self {
        Self::uint64_binary(
            left,
            right,
            |left, right| Some(left.wrapping_add(right)),
            Self::UInt64Add,
        )
    }

    pub(crate) fn uint64_subtract(left: Self, right: Self) -> Self {
        Self::uint64_binary(
            left,
            right,
            |left, right| Some(left.wrapping_sub(right)),
            Self::UInt64Subtract,
        )
    }

    pub(crate) fn uint64_multiply(left: Self, right: Self) -> Self {
        Self::uint64_binary(
            left,
            right,
            |left, right| Some(left.wrapping_mul(right)),
            Self::UInt64Multiply,
        )
    }

    pub(crate) fn uint64_divide(left: Self, right: Self) -> Self {
        Self::uint64_binary(
            left,
            right,
            |left, right| (right != 0).then_some(left / right),
            Self::UInt64Divide,
        )
    }

    pub(crate) fn uint64_remainder(left: Self, right: Self) -> Self {
        Self::uint64_binary(
            left,
            right,
            |left, right| (right != 0).then_some(left % right),
            Self::UInt64Remainder,
        )
    }

    pub(crate) fn uint64_shift_left(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if count < 64 => {
                Self::UInt64Constant(left.wrapping_shl(count))
            }
            _ => Self::UInt64ShiftLeft(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_logical_shift_right(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) if count < 64 => Self::UInt64Constant(left >> count),
            _ => Self::UInt64LogicalShiftRight(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_bitwise_and(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => Self::UInt64Constant(left & right),
            _ => Self::UInt64BitwiseAnd(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_bitwise_or(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => Self::UInt64Constant(left | right),
            _ => Self::UInt64BitwiseOr(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_bitwise_xor(left: Self, right: Self) -> Self {
        match (uint64_constant(&left), uint64_constant(&right)) {
            (Some(left), Some(right)) => Self::UInt64Constant(left ^ right),
            _ => Self::UInt64BitwiseXor(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_bitwise_not(value: Self) -> Self {
        match uint64_constant(&value) {
            Some(value) => Self::UInt64Constant(!value),
            None => Self::UInt64BitwiseNot(Box::new(value)),
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
            Self::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => {
                let value = if *unsigned {
                    i64::try_from(value.uint64_as_const()?).ok()?
                } else {
                    value.int64_as_const()?
                };
                value.checked_mul(*byte_width)
            }
        }
    }

    pub(crate) fn add(left: Self, right: Self) -> Self {
        if let (Some(left), Some(right)) = (left.as_const(), right.as_const()) {
            return Self::Constant(left + right);
        }
        if left.as_const() == Some(0) {
            return right;
        }
        if right.as_const() == Some(0) {
            return left;
        }
        // Keep a chain of constant byte displacements in one canonical
        // shape. Nested member access commonly forms `(base + outer) +
        // inner`, while aggregate copying starts from `base + total`;
        // treating those as distinct pointers would mint unrelated
        // symbolic loads for the same field.
        if let (Self::Add(base, trailing), Self::Constant(right)) = (&left, &right)
            && let Some(trailing) = trailing.as_const()
        {
            return Self::add((**base).clone(), Self::Constant(trailing + right));
        }
        Self::Add(Box::new(left), Box::new(right))
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

    pub(crate) fn scale_int64(value: Bitvector32Term, byte_width: i64, unsigned: bool) -> Self {
        let constant = if unsigned {
            value.uint64_as_const().and_then(|value| {
                i64::try_from(value)
                    .ok()
                    .and_then(|value| value.checked_mul(byte_width))
            })
        } else {
            value
                .int64_as_const()
                .and_then(|value| value.checked_mul(byte_width))
        };
        match constant {
            Some(value) => Self::Constant(value),
            None => Self::Int64Scaled {
                value: Box::new(value),
                byte_width,
                unsigned,
            },
        }
    }
}

impl ConditionTerm {
    pub(crate) fn int64_signed_less_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left < right),
            _ => Self::Bitvector64SignedLessThan(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left <= right),
            _ => Self::Bitvector64SignedLessEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left > right),
            _ => Self::Bitvector64SignedGreaterThan(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_greater_equal(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left >= right),
            _ => Self::Bitvector64SignedGreaterEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_less_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left < right),
            _ => Self::Bitvector64UnsignedLessThan(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left <= right),
            _ => Self::Bitvector64UnsignedLessEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left > right),
            _ => Self::Bitvector64UnsignedGreaterThan(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_greater_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left >= right),
            _ => Self::Bitvector64UnsignedGreaterEqual(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        if left == right {
            return Self::Constant(true);
        }
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::Bitvector64Equal(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn uint64_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        if left == right {
            return Self::Constant(true);
        }
        match (left.uint64_as_const(), right.uint64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left == right),
            _ => Self::Bitvector64Equal(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_add_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left.checked_add(right).is_none()),
            _ => Self::Bitvector64SignedAddOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_subtract_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left.checked_sub(right).is_none()),
            _ => Self::Bitvector64SignedSubtractOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_multiply_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => Self::Constant(left.checked_mul(right).is_none()),
            _ => Self::Bitvector64SignedMultiplyOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_divide_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.int64_as_const(), right.int64_as_const()) {
            (Some(left), Some(right)) => {
                Self::Constant(right == 0 || (left == i64::MIN && right == -1))
            }
            _ => Self::Bitvector64SignedDivideOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn int64_signed_shift_left_overflows(
        left: Bitvector32Term,
        right: Bitvector32Term,
    ) -> Self {
        match (left.int64_as_const(), int64_shift_count_constant(&right)) {
            (Some(left), Some(count)) => Self::Constant(
                count >= 64 || left < 0 || left.checked_shl(count).is_none_or(|result| result < 0),
            ),
            _ => Self::Bitvector64SignedShiftLeftOverflows(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn unsigned_less_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        let sign_bit = Bitvector32Term::Constant(0x8000_0000);
        Self::signed_less_than(
            Bitvector32Term::bitwise_xor(left, sign_bit.clone()),
            Bitvector32Term::bitwise_xor(right, sign_bit),
        )
    }

    pub(crate) fn unsigned_less_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        let sign_bit = Bitvector32Term::Constant(0x8000_0000);
        Self::signed_less_equal(
            Bitvector32Term::bitwise_xor(left, sign_bit.clone()),
            Bitvector32Term::bitwise_xor(right, sign_bit),
        )
    }

    pub(crate) fn unsigned_greater_than(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        let sign_bit = Bitvector32Term::Constant(0x8000_0000);
        Self::signed_greater_than(
            Bitvector32Term::bitwise_xor(left, sign_bit.clone()),
            Bitvector32Term::bitwise_xor(right, sign_bit),
        )
    }

    pub(crate) fn unsigned_greater_equal(left: Bitvector32Term, right: Bitvector32Term) -> Self {
        let sign_bit = Bitvector32Term::Constant(0x8000_0000);
        Self::signed_greater_equal(
            Bitvector32Term::bitwise_xor(left, sign_bit.clone()),
            Bitvector32Term::bitwise_xor(right, sign_bit),
        )
    }

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
        if right.as_const() == Some(0) {
            return Self::Constant(false);
        }
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
    pub(crate) fn function_pointer_signature(return_type: Self, parameter_types: &[Self]) -> u64 {
        // Pack the finite modeled type alphabet into nibbles. This is exact,
        // unlike a hash, so an incompatible callback can never be admitted by
        // a signature collision. The high-level C parser caps callback arity
        // at thirteen, which fits the key in one u64.
        fn code(c_type: CType) -> Option<u64> {
            Some(match c_type {
                CType::Void => 0,
                CType::Int32 => 1,
                CType::UInt8 => 2,
                CType::UInt32 => 3,
                CType::Int32Pointer => 4,
                CType::UInt8Pointer => 5,
                CType::Int32PointerPointer => 6,
                CType::UInt8PointerPointer => 7,
                CType::Int16 => 8,
                CType::UInt16 => 9,
                CType::Int64 => 10,
                CType::UInt64 => 11,
                CType::Int16Pointer => 12,
                CType::UInt16Pointer => 13,
                CType::UInt32Pointer => 14,
                CType::Int64Pointer => 15,
                CType::UInt64Pointer => 16,
                CType::Float32 => 17,
                CType::Float64 => 18,
                CType::Int16PointerPointer
                | CType::UInt16PointerPointer
                | CType::UInt32PointerPointer
                | CType::Int64PointerPointer
                | CType::UInt64PointerPointer
                | CType::FunctionPointer(_)
                | CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::Int16Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int64Array(_)
                | CType::UInt64Array(_)
                | CType::Float32Pointer
                | CType::Float64Pointer
                | CType::Float32PointerPointer
                | CType::Float64PointerPointer
                | CType::Float32Array(_)
                | CType::Float64Array(_) => {
                    return None;
                }
            })
        }

        if parameter_types.len() > 13 {
            return 0;
        }
        let Some(return_code) = code(return_type) else {
            return 0;
        };
        let mut signature = 1 | ((parameter_types.len() as u64) << 1) | (return_code << 5);
        for (index, &parameter_type) in parameter_types.iter().enumerate() {
            let Some(parameter_code) = code(parameter_type) else {
                return 0;
            };
            signature |= parameter_code << (9 + index * 4);
        }
        signature
    }

    pub fn is_pointer(self) -> bool {
        self.pointee_type().is_some() || matches!(self, Self::FunctionPointer(_))
    }

    pub(crate) fn pointer_to(self) -> Option<Self> {
        match self {
            Self::Int16 => Some(Self::Int16Pointer),
            Self::Int32 => Some(Self::Int32Pointer),
            Self::UInt8 => Some(Self::UInt8Pointer),
            Self::UInt16 => Some(Self::UInt16Pointer),
            Self::UInt32 => Some(Self::UInt32Pointer),
            Self::Int64 => Some(Self::Int64Pointer),
            Self::UInt64 => Some(Self::UInt64Pointer),
            Self::Float32 => Some(Self::Float32Pointer),
            Self::Float64 => Some(Self::Float64Pointer),
            Self::Int16Pointer => Some(Self::Int16PointerPointer),
            Self::UInt16Pointer => Some(Self::UInt16PointerPointer),
            Self::Int32Pointer => Some(Self::Int32PointerPointer),
            Self::UInt8Pointer => Some(Self::UInt8PointerPointer),
            Self::UInt32Pointer => Some(Self::UInt32PointerPointer),
            Self::Int64Pointer => Some(Self::Int64PointerPointer),
            Self::UInt64Pointer => Some(Self::UInt64PointerPointer),
            Self::Float32Pointer => Some(Self::Float32PointerPointer),
            Self::Float64Pointer => Some(Self::Float64PointerPointer),
            Self::Void
            | Self::Int16PointerPointer
            | Self::UInt16PointerPointer
            | Self::Int32PointerPointer
            | Self::UInt8PointerPointer
            | Self::UInt32PointerPointer
            | Self::Int64PointerPointer
            | Self::UInt64PointerPointer
            | Self::FunctionPointer(_)
            | Self::Int32Array(_)
            | Self::UInt8Array(_)
            | Self::Int16Array(_)
            | Self::UInt16Array(_)
            | Self::UInt32Array(_)
            | Self::Int64Array(_)
            | Self::UInt64Array(_)
            | Self::Float32PointerPointer
            | Self::Float64PointerPointer
            | Self::Float32Array(_)
            | Self::Float64Array(_) => None,
        }
    }

    pub(crate) fn accepts(self, value: &CValue) -> bool {
        match (self, value) {
            (Self::Void, CValue::Void)
            | (Self::Int16, CValue::Int16(_))
            | (Self::Int32, CValue::Int32(_))
            | (Self::UInt8, CValue::UInt8(_))
            | (Self::UInt16, CValue::UInt16(_))
            | (Self::Int64, CValue::Int64(_))
            | (Self::UInt64, CValue::UInt64(_))
            | (Self::Float32, CValue::Float32(_))
            | (Self::Float64, CValue::Float64(_))
            | (Self::UInt32, CValue::UInt32(_)) => true,
            (target, CValue::Pointer(pointer)) if target.is_pointer() => {
                pointer.is_null()
                    || (pointer.c_type() == target
                        && if target.is_function_pointer() {
                            pointer.block.is_function()
                        } else {
                            !pointer.block.is_function()
                        })
            }
            _ => false,
        }
    }

    pub fn byte_width(self) -> u32 {
        match self {
            Self::Void => 0,
            Self::Int16 => 2,
            Self::Int32 => 4,
            Self::UInt8 => 1,
            Self::UInt16 => 2,
            Self::UInt32 => 4,
            Self::Int64 => 8,
            Self::UInt64 => 8,
            Self::Float32 => 4,
            Self::Float64 => 8,
            Self::Int16Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int32Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt8Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt16Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt32Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int64Pointer => C_POINTER_BYTE_WIDTH,
            Self::UInt64Pointer => C_POINTER_BYTE_WIDTH,
            Self::Float32Pointer => C_POINTER_BYTE_WIDTH,
            Self::Float64Pointer => C_POINTER_BYTE_WIDTH,
            Self::Int16PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Int32PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt8PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt16PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt32PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Int64PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::UInt64PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Float32PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::Float64PointerPointer => C_POINTER_BYTE_WIDTH,
            Self::FunctionPointer(_) => C_POINTER_BYTE_WIDTH,
            Self::Int32Array(length) => length.saturating_mul(4),
            Self::UInt8Array(length) => length,
            Self::Int16Array(length) | Self::UInt16Array(length) => length.saturating_mul(2),
            Self::UInt32Array(length) => length.saturating_mul(4),
            Self::Int64Array(length) | Self::UInt64Array(length) => length.saturating_mul(8),
            Self::Float32Array(length) => length.saturating_mul(4),
            Self::Float64Array(length) => length.saturating_mul(8),
        }
    }

    pub fn pointee_type(self) -> Option<Self> {
        match self {
            Self::Int16Pointer => Some(Self::Int16),
            Self::Int32Pointer => Some(Self::Int32),
            Self::UInt8Pointer => Some(Self::UInt8),
            Self::UInt16Pointer => Some(Self::UInt16),
            Self::UInt32Pointer => Some(Self::UInt32),
            Self::Int64Pointer => Some(Self::Int64),
            Self::UInt64Pointer => Some(Self::UInt64),
            Self::Int16PointerPointer => Some(Self::Int16Pointer),
            Self::Int32PointerPointer => Some(Self::Int32Pointer),
            Self::UInt8PointerPointer => Some(Self::UInt8Pointer),
            Self::UInt16PointerPointer => Some(Self::UInt16Pointer),
            Self::UInt32PointerPointer => Some(Self::UInt32Pointer),
            Self::Int64PointerPointer => Some(Self::Int64Pointer),
            Self::UInt64PointerPointer => Some(Self::UInt64Pointer),
            Self::Float32Pointer => Some(Self::Float32),
            Self::Float64Pointer => Some(Self::Float64),
            Self::Float32PointerPointer => Some(Self::Float32Pointer),
            Self::Float64PointerPointer => Some(Self::Float64Pointer),
            _ => None,
        }
    }

    fn is_function_pointer(self) -> bool {
        matches!(self, Self::FunctionPointer(_))
    }
}

impl CValue {
    pub(crate) fn pointer(pointer: Pointer) -> Self {
        Self::typed_pointer(pointer, CType::Int32Pointer)
    }

    pub(crate) fn typed_pointer(pointer: Pointer, c_type: CType) -> Self {
        Self::Pointer(CPointerValue::new(pointer, c_type))
    }

    pub(crate) fn typed_pointer_with_pointee_volatile(
        pointer: Pointer,
        c_type: CType,
        pointee_volatile: bool,
    ) -> Self {
        Self::Pointer(CPointerValue::new(pointer, c_type).with_pointee_volatile(pointee_volatile))
    }

    pub(crate) fn retag_pointer(self, c_type: CType) -> Self {
        match self {
            Self::Pointer(pointer) => Self::Pointer(pointer.with_type(c_type)),
            value => value,
        }
    }

    pub(crate) fn with_pointer_pointee_volatile(self, pointee_volatile: bool) -> Self {
        match self {
            Self::Pointer(pointer) => {
                Self::Pointer(pointer.with_pointee_volatile(pointee_volatile))
            }
            value => value,
        }
    }

    pub(crate) fn c_type(&self) -> CType {
        match self {
            Self::Void => CType::Void,
            Self::Int16(_) => CType::Int16,
            Self::Int32(_) => CType::Int32,
            Self::UInt8(_) => CType::UInt8,
            Self::UInt16(_) => CType::UInt16,
            Self::UInt32(_) => CType::UInt32,
            Self::Int64(_) => CType::Int64,
            Self::UInt64(_) => CType::UInt64,
            Self::Float32(_) => CType::Float32,
            Self::Float64(_) => CType::Float64,
            Self::Pointer(pointer) => pointer.c_type(),
        }
    }

    pub(in crate::kernel) fn byte_width(&self) -> u32 {
        match self {
            Self::Void => 0,
            Self::Int16(_) => 2,
            Self::Int32(_) => 4,
            Self::UInt8(_) => 1,
            Self::UInt16(_) => 2,
            Self::UInt32(_) => 4,
            Self::Int64(_) => 8,
            Self::UInt64(_) => 8,
            Self::Float32(_) => 4,
            Self::Float64(_) => 8,
            Self::Pointer(_) => C_POINTER_BYTE_WIDTH,
        }
    }
}

impl CLValue {
    pub(in crate::kernel) fn local(name: impl Into<String>, value_type: CType) -> Self {
        Self::local_with_qualifiers(name, value_type, false, false)
    }

    pub(in crate::kernel) fn local_with_volatile(
        name: impl Into<String>,
        value_type: CType,
        volatile: bool,
    ) -> Self {
        Self::local_with_qualifiers(name, value_type, volatile, false)
    }

    pub(in crate::kernel) fn local_with_qualifiers(
        name: impl Into<String>,
        value_type: CType,
        volatile: bool,
        pointee_volatile: bool,
    ) -> Self {
        Self {
            storage: CLValueStorage::Local { name: name.into() },
            value_type,
            volatile,
            pointee_volatile,
        }
    }

    pub(in crate::kernel) fn memory(pointer: Pointer, value_type: CType) -> Self {
        Self::memory_with_qualifiers(pointer, value_type, false, false)
    }

    pub(in crate::kernel) fn memory_with_volatile(
        pointer: Pointer,
        value_type: CType,
        volatile: bool,
    ) -> Self {
        Self::memory_with_qualifiers(pointer, value_type, volatile, false)
    }

    pub(in crate::kernel) fn memory_with_qualifiers(
        pointer: Pointer,
        value_type: CType,
        volatile: bool,
        pointee_volatile: bool,
    ) -> Self {
        Self {
            storage: CLValueStorage::Memory { pointer },
            value_type,
            volatile,
            pointee_volatile,
        }
    }

    pub fn value_type(&self) -> CType {
        self.value_type
    }

    pub(in crate::kernel) fn is_volatile(&self) -> bool {
        self.volatile
    }

    pub(in crate::kernel) fn pointee_is_volatile(&self) -> bool {
        self.pointee_volatile
    }

    pub(in crate::kernel) fn pointer(&self, state: &CState) -> Option<Pointer> {
        match &self.storage {
            CLValueStorage::Local { name } => {
                let pointer = state.locals.slot(name)?.clone();
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

    pub(crate) fn symbolic_function(variable: Variable) -> Self {
        Self {
            block: PointerBlock::FunctionSymbolic(variable),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    pub(crate) fn function(name: impl Into<String>) -> Self {
        Self {
            block: PointerBlock::Function(name.into()),
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
        // A function's own scalar locals (`local:` blocks) are storage the
        // function declared; memory reached through a parameter
        // (`ExternalArgument`) existed before the call and cannot be one of
        // them.
        let local_versus_argument = |left: &PointerBlock, right: &PointerBlock| {
            left.starts_with("local:") && matches!(right, PointerBlock::ExternalArgument)
        };
        self.block != other.block
            && (matches!(self.block, PointerBlock::Heap(_))
                || matches!(other.block, PointerBlock::Heap(_))
                || matches!(
                    (&self.block, &other.block),
                    (PointerBlock::Concrete(left), PointerBlock::Concrete(right)) if left != right
                )
                || local_versus_argument(&self.block, &other.block)
                || local_versus_argument(&other.block, &self.block))
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

    pub(in crate::kernel) fn offset_by_typed_elements(
        &self,
        elements: Bitvector32Term,
        byte_width: u32,
        unsigned: bool,
        wide: bool,
    ) -> Self {
        Self {
            block: self.block.clone(),
            offset: PointerOffsetTerm::add(
                self.offset.clone(),
                if wide {
                    PointerOffsetTerm::scale_int64(elements, i64::from(byte_width), unsigned)
                } else {
                    PointerOffsetTerm::scale_int32(elements, i64::from(byte_width))
                },
            ),
        }
    }

    pub(crate) fn element_index_from_base(&self, base: &Self) -> Option<Bitvector32Term> {
        self.element_index_from_base_with_width(base, 4)
    }

    pub(crate) fn element_index_from_base_with_width(
        &self,
        base: &Self,
        byte_width: u32,
    ) -> Option<Bitvector32Term> {
        if self.block != base.block {
            return None;
        }

        if self.offset == base.offset {
            return Some(Bitvector32Term::Constant(0));
        }

        if base.offset == PointerOffsetTerm::Constant(0) {
            return crate::kernel::reasoning::element_index_from_offset(&self.offset, byte_width);
        }

        match &self.offset {
            PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
                crate::kernel::reasoning::element_index_from_offset(right, byte_width)
            }
            PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
                crate::kernel::reasoning::element_index_from_offset(left, byte_width)
            }
            _ => {
                if let (Some(pointer_index), Some(base_index)) = (
                    crate::kernel::reasoning::element_index_from_offset(&self.offset, byte_width),
                    crate::kernel::reasoning::element_index_from_offset(&base.offset, byte_width),
                ) {
                    Some(Bitvector32Term::subtract(pointer_index, base_index))
                } else {
                    None
                }
            }
        }
    }
}
