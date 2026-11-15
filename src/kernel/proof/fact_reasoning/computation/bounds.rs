//! Intrinsic intervals of the selected arithmetic DAG. No facts, read
//! resolution, call unfolding, or fold evaluation. Unknown machine operands
//! have only their type's range; an unknown Integer has no finite interval.
use super::*;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::HashMap;

type Interval = (BigInt, BigInt);
#[derive(Default)]
struct Bounds {
    integer: HashMap<u64, Option<Interval>>,
    machine: HashMap<(u8, u64, MachineIntegerType), Interval>,
    boolean: HashMap<(u8, u64), Option<bool>>,
}

fn work(bounds: &Interval) -> bool {
    !crate::instrumentation::deadline_exceeded_with_work(
        (bounds.0.bits() + bounds.1.bits()) as usize + 1,
    )
}
fn hull(a: Interval, b: Interval) -> Interval {
    (a.0.min(b.0), a.1.max(b.1))
}
fn clip(range: Interval, format: MachineIntegerType) -> Interval {
    let (min, max) = format.format().bounds();
    if min <= range.0 && range.1 <= max {
        return range;
    }
    if range.0 == range.1 {
        let modulus = &max - &min + BigInt::one();
        let value = ((range.0 - &min) % &modulus + &modulus) % modulus + min;
        return (value.clone(), value);
    }
    (min, max)
}
impl Bounds {
    fn boolean(&mut self, view: BooleanOperandView<'_>) -> Option<bool> {
        let key = match view {
            BooleanOperandView::Shared(root) => (0, root.id()),
            BooleanOperandView::Native(root) => (1, root as *const ConditionTerm as usize as u64),
        };
        if let Some(found) = self.boolean.get(&key) {
            return *found;
        }
        crate::instrumentation::record_deterministic_work(1);
        let value = if let Some(value) = view.constant() {
            Some(value)
        } else if let Some((format, relation, [left, right])) = view.comparison() {
            let identical = (left.variable().is_some() && left.variable() == right.variable())
                || match (left, right) {
                    (MachineOperandView::Shared(a), MachineOperandView::Shared(b)) => a == b,
                    (MachineOperandView::Legacy(a), MachineOperandView::Legacy(b)) => a == b,
                    _ => false,
                };
            if identical {
                Some(matches!(
                    relation,
                    CompareRelation::Equal
                        | CompareRelation::LessEqual
                        | CompareRelation::GreaterEqual
                ))
            } else {
                decide(
                    self.machine(left, format)?,
                    self.machine(right, format)?,
                    relation,
                )
            }
        } else {
            None
        };
        self.boolean.insert(key, value);
        value
    }

    fn machine(
        &mut self,
        term: MachineOperandView<'_>,
        format: MachineIntegerType,
    ) -> Option<Interval> {
        let key = match term {
            MachineOperandView::Shared(root) => (0, root.id(), format),
            MachineOperandView::Legacy(root) => {
                (1, root as *const MachineTerm as usize as u64, format)
            }
        };
        if let Some(found) = self.machine.get(&key) {
            return Some(found.clone());
        }
        crate::instrumentation::record_deterministic_work(1);
        let result = if let Some(literal) = term
            .literal()
            .and_then(|value| format.constant_from_term(&value))
        {
            let value = literal.to_integer();
            (value.clone(), value)
        } else if let Some((guard, arms)) = term.conditional_view() {
            match self.boolean(guard) {
                Some(true) => self.machine(arms[0], format)?,
                Some(false) => self.machine(arms[1], format)?,
                None => hull(
                    self.machine(arms[0], format)?,
                    self.machine(arms[1], format)?,
                ),
            }
        } else if let Some((_, from, to, operand)) = term.cast() {
            let range = self.machine(operand, from)?;
            clip(clip(range, to), format)
        } else if let Some((op_format, op, operands)) = term.binary() {
            let a = self.machine(operands[0], op_format)?;
            let b = self.machine(operands[1], op_format)?;
            let range = match op {
                MachineBinaryOp::Add => (a.0 + b.0, a.1 + b.1),
                MachineBinaryOp::Subtract => (a.0 - b.1, a.1 - b.0),
                MachineBinaryOp::Multiply => {
                    let values = [&a.0 * &b.0, &a.0 * &b.1, &a.1 * &b.0, &a.1 * &b.1];
                    (values.iter().min()?.clone(), values.iter().max()?.clone())
                }
                MachineBinaryOp::BitwiseAnd if b.0 == b.1 && b.0 >= BigInt::zero() => {
                    (BigInt::zero(), b.0)
                }
                MachineBinaryOp::BitwiseAnd if a.0 == a.1 && a.0 >= BigInt::zero() => {
                    (BigInt::zero(), a.0)
                }
                MachineBinaryOp::Divide
                    if b.0 == b.1 && b.0 > BigInt::zero() && a.0 >= BigInt::zero() =>
                {
                    (a.0 / &b.0, a.1 / b.0)
                }
                MachineBinaryOp::Remainder
                    if b.0 == b.1 && b.0 > BigInt::zero() && a.0 >= BigInt::zero() =>
                {
                    (BigInt::zero(), a.1.min(b.0 - 1))
                }
                _ => op_format.format().bounds(),
            };
            clip(clip(range, op_format), format)
        } else {
            // Every machine term denotes a value of its explicitly selected
            // format. Do not inspect the payload of a read, call or fold.
            format.format().bounds()
        };
        if !work(&result) {
            return None;
        }
        self.machine.insert(key, result.clone());
        Some(result)
    }
    fn integer(&mut self, term: &SharedIntegerTerm) -> Option<Interval> {
        if let Some(found) = self.integer.get(&term.id()) {
            return found.clone();
        }
        crate::instrumentation::record_deterministic_work(1);
        let result = match term.as_ref() {
            IntegerTerm::Constant(value) => {
                if crate::instrumentation::deadline_exceeded_with_work(value.bits() as usize + 1) {
                    return None;
                }
                Some((value.clone(), value.clone()))
            }
            IntegerTerm::Machine(value) => self.machine(value.operand_view(), value.ty()),
            IntegerTerm::If {
                then_term,
                else_term,
                ..
            } => Some(hull(self.integer(then_term)?, self.integer(else_term)?)),
            IntegerTerm::Negate(value) => {
                let (low, high) = self.integer(value)?;
                Some((-high, -low))
            }
            IntegerTerm::Add(left, right) => {
                let a = self.integer(left)?;
                let b = self.integer(right)?;
                if !work(&a) || !work(&b) {
                    return None;
                }
                Some((a.0 + b.0, a.1 + b.1))
            }
            IntegerTerm::Subtract(left, right) => {
                let a = self.integer(left)?;
                let b = self.integer(right)?;
                if !work(&a) || !work(&b) {
                    return None;
                }
                Some((a.0 - b.1, a.1 - b.0))
            }
            _ => None,
        };
        if let Some(result) = &result {
            if !work(result) {
                return None;
            }
        }
        self.integer.insert(term.id(), result.clone());
        result
    }
}

pub(super) fn machine_bounds(term: &MachineTerm, format: MachineIntegerType) -> Option<Interval> {
    Bounds::default().machine(MachineOperandView::Legacy(term), format)
}

pub(super) fn comparison(condition: &ConditionTerm) -> Option<bool> {
    let mut bounds = Bounds::default();
    let (left, right, relation, negate) = match condition {
        ConditionTerm::Compare {
            format,
            relation,
            left,
            right,
        } => (
            bounds.machine(MachineOperandView::Legacy(left), *format)?,
            bounds.machine(MachineOperandView::Legacy(right), *format)?,
            *relation,
            false,
        ),
        ConditionTerm::IntegerEqual(a, b)
        | ConditionTerm::IntegerNotEqual(a, b)
        | ConditionTerm::IntegerLessThan(a, b)
        | ConditionTerm::IntegerLessEqual(a, b)
        | ConditionTerm::IntegerGreaterThan(a, b)
        | ConditionTerm::IntegerGreaterEqual(a, b) => {
            let relation = match condition {
                ConditionTerm::IntegerEqual(..) | ConditionTerm::IntegerNotEqual(..) => {
                    CompareRelation::Equal
                }
                ConditionTerm::IntegerLessThan(..) => CompareRelation::LessThan,
                ConditionTerm::IntegerLessEqual(..) => CompareRelation::LessEqual,
                ConditionTerm::IntegerGreaterThan(..) => CompareRelation::GreaterThan,
                _ => CompareRelation::GreaterEqual,
            };
            (
                bounds.integer(a)?,
                bounds.integer(b)?,
                relation,
                matches!(condition, ConditionTerm::IntegerNotEqual(..)),
            )
        }
        _ => return None,
    };
    decide(left, right, relation).map(|value| value != negate)
}

fn decide(left: Interval, right: Interval, relation: CompareRelation) -> Option<bool> {
    let (left, right, relation) = match relation {
        CompareRelation::GreaterThan => (right, left, CompareRelation::LessThan),
        CompareRelation::GreaterEqual => (right, left, CompareRelation::LessEqual),
        relation => (left, right, relation),
    };
    let value = match relation {
        CompareRelation::Equal if left.0 == left.1 && right.0 == right.1 && left.0 == right.0 => {
            true
        }
        CompareRelation::Equal if left.1 < right.0 || right.1 < left.0 => false,
        CompareRelation::LessThan if left.1 < right.0 => true,
        CompareRelation::LessThan if left.0 >= right.1 => false,
        CompareRelation::LessEqual if left.1 <= right.0 => true,
        CompareRelation::LessEqual if left.0 > right.1 => false,
        _ => return None,
    };
    Some(value)
}
