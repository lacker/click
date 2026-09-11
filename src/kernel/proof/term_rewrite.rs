//! Sort-preserving congruence and explicitly directed conditional reduction.
//! Memory snapshots are opaque: this walks the selected logical expression,
//! never a heap or an ambient proof state.
use crate::kernel::*;
use crate::kernel::{
    AlgebraicBitvectorMatchArm, AlgebraicResultMatchArm, AlgebraicTerm, AlgebraicTermNode,
    AlgebraicValue, PureFunctionArgument,
};
#[cfg(test)]
use std::collections::BTreeMap;
use std::collections::HashMap;

pub(crate) struct TermRewrite<'a> {
    algebraic: Option<(&'a AlgebraicTerm, &'a AlgebraicTerm)>,
    bitvector: Option<(&'a Bitvector32Term, &'a Bitvector32Term)>,
    pointer_variable: Option<(Variable, &'a Pointer)>,
    conditions: Option<&'a HashMap<ConditionTerm, bool>>,
    collected_conditions: Option<Vec<ConditionTerm>>,
    integer_cache: HashMap<u64, IntegerTerm>,
    pub(crate) changed: bool,
    #[cfg(test)]
    pub(crate) visits: usize,
}
impl<'a> TermRewrite<'a> {
    pub(crate) fn new(from: &'a AlgebraicTerm, to: &'a AlgebraicTerm) -> Self {
        Self {
            conditions: None,
            collected_conditions: None,
            algebraic: Some((from, to)),
            bitvector: None,
            changed: false,
            integer_cache: HashMap::new(),
            pointer_variable: None,
            #[cfg(test)]
            visits: 0,
        }
    }
    pub(crate) fn for_bits(from: &'a Bitvector32Term, to: &'a Bitvector32Term) -> Self {
        Self {
            conditions: None,
            collected_conditions: None,
            algebraic: None,
            bitvector: Some((from, to)),
            changed: false,
            integer_cache: HashMap::new(),
            pointer_variable: None,
            #[cfg(test)]
            visits: 0,
        }
    }
    pub(crate) fn for_conditions(conditions: &'a HashMap<ConditionTerm, bool>) -> Self {
        Self {
            algebraic: None,
            bitvector: None,
            conditions: Some(conditions),
            collected_conditions: None,
            changed: false,
            integer_cache: HashMap::new(),
            pointer_variable: None,
            #[cfg(test)]
            visits: 0,
        }
    }
    pub(crate) fn for_pointer_variable(from: Variable, to: &'a Pointer) -> Self {
        Self {
            algebraic: None,
            bitvector: None,
            pointer_variable: Some((from, to)),
            conditions: None,
            collected_conditions: None,
            integer_cache: HashMap::new(),
            changed: false,
            #[cfg(test)]
            visits: 0,
        }
    }

    pub(crate) fn conditional_guards(proposition: &Proposition) -> Vec<ConditionTerm> {
        let empty = HashMap::new();
        let mut walker = TermRewrite::for_conditions(&empty);
        walker.collected_conditions = Some(Vec::new());
        walker.proposition(proposition);
        walker.collected_conditions.unwrap()
    }

    pub(crate) fn proposition(&mut self, proposition: &Proposition) -> Proposition {
        match proposition {
            Proposition::Equal(a, b) => Proposition::Equal(self.term(a), self.term(b)),
            Proposition::ConditionIs(c, value) => {
                Proposition::ConditionIs(self.condition(c), *value)
            }
            Proposition::Not(p) => Proposition::Not(Box::new(self.proposition(p))),
            // Binder-bearing and compound propositions require their own explicit proof steps.
            _ => proposition.clone(),
        }
    }
    fn visit(&mut self) {
        crate::instrumentation::record_deterministic_work(1);
        #[cfg(test)]
        {
            self.visits += 1;
        }
    }
    pub(crate) fn term(&mut self, term: &Term) -> Term {
        self.visit();
        match term {
            Term::Algebraic(v) => Term::Algebraic(self.algebraic(v)),
            Term::Bitvector32(v) => Term::Bitvector32(self.bits(v)),
            Term::Integer(v) => Term::Integer(self.integer(v)),
            Term::CValue(v) => Term::CValue(self.value(v)),
            Term::Condition(v) => Term::Condition(self.condition(v)),
            Term::PointerOffset(v) => Term::PointerOffset(self.offset(v)),
            _ => term.clone(),
        }
    }
    fn algebraic(&mut self, term: &AlgebraicTerm) -> AlgebraicTerm {
        self.visit();
        if let Some((from, to)) = self.algebraic
            && term == from
        {
            self.changed = true;
            return to.clone();
        }
        let node = match &term.node {
            AlgebraicTermNode::Variable(v) => AlgebraicTermNode::Variable(*v),
            AlgebraicTermNode::Constructor { variant, fields } => AlgebraicTermNode::Constructor {
                variant: variant.clone(),
                fields: fields.iter().map(|v| self.field(v)).collect(),
            },
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                AlgebraicTermNode::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments.iter().map(|a| self.argument(a)).collect(),
                }
            }
            AlgebraicTermNode::Match { scrutinee, arms } => AlgebraicTermNode::Match {
                scrutinee: Box::new(self.algebraic(scrutinee)),
                arms: arms
                    .iter()
                    .map(|a| AlgebraicResultMatchArm {
                        variant: a.variant.clone(),
                        bindings: a.bindings.clone(),
                        body: if self.conditions.is_some() {
                            a.body.clone()
                        } else {
                            self.algebraic(&a.body)
                        },
                    })
                    .collect(),
            },
        };
        AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node,
        }
    }
    fn field(&mut self, v: &AlgebraicValue) -> AlgebraicValue {
        match v {
            AlgebraicValue::C(v) => AlgebraicValue::C(self.value(v)),
            AlgebraicValue::Integer(v) => AlgebraicValue::Integer(v.clone()),
            AlgebraicValue::Algebraic(v) => AlgebraicValue::Algebraic(self.algebraic(v)),
        }
    }
    fn argument(&mut self, a: &PureFunctionArgument) -> PureFunctionArgument {
        match a {
            PureFunctionArgument::Value(v) => PureFunctionArgument::Value(self.value(v)),
            PureFunctionArgument::Algebraic(v) => {
                PureFunctionArgument::Algebraic(self.algebraic(v))
            }
            PureFunctionArgument::ArrayRef {
                memory,
                pointer,
                element_type,
            } => PureFunctionArgument::ArrayRef {
                memory: memory.clone(),
                pointer: self.value(pointer),
                element_type: *element_type,
            },
        }
    }
    fn value(&mut self, v: &CValue) -> CValue {
        match v {
            CValue::Void => CValue::Void,
            CValue::Bool(v) => CValue::Bool(self.bits(v)),
            CValue::Int16(v) => CValue::Int16(self.bits(v)),
            CValue::UInt16(v) => CValue::UInt16(self.bits(v)),
            CValue::UInt8(v) => CValue::UInt8(self.bits(v)),
            CValue::Int32(v) => CValue::Int32(self.bits(v)),
            CValue::UInt32(v) => CValue::UInt32(self.bits(v)),
            CValue::Int64(v) => CValue::Int64(self.bits(v)),
            CValue::UInt64(v) => CValue::UInt64(self.bits(v)),
            CValue::Float32(v) => CValue::Float32(self.bits(v)),
            CValue::Float64(v) => CValue::Float64(self.bits(v)),
            CValue::Pointer(v) => {
                let mut result = v.clone();
                result.replace_pointer(self.pointer(v.pointer()));
                CValue::Pointer(result)
            }
        }
    }
    fn integer(&mut self, v: &IntegerTerm) -> IntegerTerm {
        self.visit();
        self.integer_shared(&SharedIntegerTerm::from(v.clone()))
    }
    fn integer_shared(&mut self, shared: &SharedIntegerTerm) -> IntegerTerm {
        if let Some(result) = self.integer_cache.get(&shared.id()) {
            return result.clone();
        }
        self.visit();
        let result = match shared.as_ref() {
            IntegerTerm::Constant(_) | IntegerTerm::Variable(_) => shared.as_ref().clone(),
            IntegerTerm::Machine(value) => {
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    value.ty(),
                    self.bits(value.value()),
                ))
            }
            // Rewriting preserves the symbolic DAG. In particular, it must
            // not fold a repeated symbolic expression into a giant literal.
            IntegerTerm::Negate(value) => IntegerTerm::Negate(self.integer_shared(value).into()),
            IntegerTerm::Add(left, right) => IntegerTerm::Add(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
            IntegerTerm::Subtract(left, right) => IntegerTerm::Subtract(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
            IntegerTerm::Multiply(left, right) => IntegerTerm::Multiply(
                self.integer_shared(left).into(),
                self.integer_shared(right).into(),
            ),
        };
        self.integer_cache.insert(shared.id(), result.clone());
        result
    }
    fn pointer(&mut self, p: &Pointer) -> Pointer {
        if let Some((from, to)) = self.pointer_variable
            && matches!(&p.block, PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) if *variable == from)
        {
            self.changed = true;
            return Pointer {
                block: to.block.clone(),
                offset: PointerOffsetTerm::add(to.offset.clone(), self.offset(&p.offset)),
            };
        }
        Pointer {
            block: p.block.clone(),
            offset: self.offset(&p.offset),
        }
    }
    fn offset(&mut self, v: &PointerOffsetTerm) -> PointerOffsetTerm {
        match v {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => v.clone(),
            PointerOffsetTerm::Add(a, b) => {
                PointerOffsetTerm::Add(Box::new(self.offset(a)), Box::new(self.offset(b)))
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                PointerOffsetTerm::Int32Scaled {
                    value: Box::new(self.bits(value)),
                    byte_width: *byte_width,
                }
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => PointerOffsetTerm::Int64Scaled {
                value: Box::new(self.bits(value)),
                byte_width: *byte_width,
                unsigned: *unsigned,
            },
        }
    }
    pub(crate) fn condition(&mut self, v: &ConditionTerm) -> ConditionTerm {
        self.visit();
        if let Some(conditions) = self.conditions
            && let Some(value) = conditions.get(v)
        {
            return ConditionTerm::Constant(*value);
        }
        match v {
            ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => v.clone(),
            ConditionTerm::AlgebraicEqual(a, b) => ConditionTerm::AlgebraicEqual(
                Box::new(self.algebraic(a)),
                Box::new(self.algebraic(b)),
            ),
            ConditionTerm::Bitvector32SignedLessThan(a, b) => {
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32SignedLessEqual(a, b) => {
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32SignedGreaterThan(a, b) => {
                ConditionTerm::Bitvector32SignedGreaterThan(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(a, b) => {
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32Equal(a, b) => {
                ConditionTerm::Bitvector32Equal(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            ConditionTerm::Bitvector32SignedAddOverflows(a, b) => {
                ConditionTerm::Bitvector32SignedAddOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32SignedSubtractOverflows(a, b) => {
                ConditionTerm::Bitvector32SignedSubtractOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32SignedMultiplyOverflows(a, b) => {
                ConditionTerm::Bitvector32SignedMultiplyOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32SignedDivideOverflows(a, b) => {
                ConditionTerm::Bitvector32SignedDivideOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(a, b) => {
                ConditionTerm::Bitvector32SignedShiftLeftOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedLessThan(a, b) => {
                ConditionTerm::Bitvector64SignedLessThan(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedLessEqual(a, b) => {
                ConditionTerm::Bitvector64SignedLessEqual(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedGreaterThan(a, b) => {
                ConditionTerm::Bitvector64SignedGreaterThan(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedGreaterEqual(a, b) => {
                ConditionTerm::Bitvector64SignedGreaterEqual(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64UnsignedLessThan(a, b) => {
                ConditionTerm::Bitvector64UnsignedLessThan(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64UnsignedLessEqual(a, b) => {
                ConditionTerm::Bitvector64UnsignedLessEqual(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64UnsignedGreaterThan(a, b) => {
                ConditionTerm::Bitvector64UnsignedGreaterThan(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64UnsignedGreaterEqual(a, b) => {
                ConditionTerm::Bitvector64UnsignedGreaterEqual(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64Equal(a, b) => {
                ConditionTerm::Bitvector64Equal(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            ConditionTerm::Bitvector64SignedAddOverflows(a, b) => {
                ConditionTerm::Bitvector64SignedAddOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedSubtractOverflows(a, b) => {
                ConditionTerm::Bitvector64SignedSubtractOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedMultiplyOverflows(a, b) => {
                ConditionTerm::Bitvector64SignedMultiplyOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedDivideOverflows(a, b) => {
                ConditionTerm::Bitvector64SignedDivideOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Bitvector64SignedShiftLeftOverflows(a, b) => {
                ConditionTerm::Bitvector64SignedShiftLeftOverflows(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            ConditionTerm::Float32(c) => {
                ConditionTerm::Float32(c.map_bitvector_terms(|b| self.bits(b)))
            }
            ConditionTerm::Float64(c) => {
                ConditionTerm::Float64(c.map_bitvector_terms(|b| self.bits(b)))
            }
            ConditionTerm::PointerEqual(a, b) => {
                ConditionTerm::PointerEqual(Box::new(self.pointer(a)), Box::new(self.pointer(b)))
            }
            ConditionTerm::PointerOffsetEqual(a, b) => ConditionTerm::PointerOffsetEqual(
                Box::new(self.offset(a)),
                Box::new(self.offset(b)),
            ),
            ConditionTerm::IntegerLessThan(a, b) => {
                ConditionTerm::integer_less_than(self.integer(a), self.integer(b))
            }
            ConditionTerm::IntegerLessEqual(a, b) => {
                ConditionTerm::integer_less_equal(self.integer(a), self.integer(b))
            }
            ConditionTerm::IntegerGreaterThan(a, b) => {
                ConditionTerm::integer_greater_than(self.integer(a), self.integer(b))
            }
            ConditionTerm::IntegerGreaterEqual(a, b) => {
                ConditionTerm::integer_greater_equal(self.integer(a), self.integer(b))
            }
            ConditionTerm::IntegerEqual(a, b) => {
                ConditionTerm::integer_equal(self.integer(a), self.integer(b))
            }
            ConditionTerm::IntegerNotEqual(a, b) => {
                ConditionTerm::integer_not_equal(self.integer(a), self.integer(b))
            }
        }
    }
    pub(crate) fn bits(&mut self, v: &Bitvector32Term) -> Bitvector32Term {
        self.visit();
        if let Some((from, to)) = self.bitvector
            && v == from
        {
            self.changed = true;
            return to.clone();
        }
        match v {
            Bitvector32Term::Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_)
            | Bitvector32Term::Variable(_) => v.clone(),
            Bitvector32Term::Add(a, b) => {
                Bitvector32Term::Add(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Subtract(a, b) => {
                Bitvector32Term::Subtract(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Multiply(a, b) => {
                Bitvector32Term::Multiply(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Divide(a, b) => {
                Bitvector32Term::Divide(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UnsignedDivide(a, b) => {
                Bitvector32Term::UnsignedDivide(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Remainder(a, b) => {
                Bitvector32Term::Remainder(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UnsignedRemainder(a, b) => {
                Bitvector32Term::UnsignedRemainder(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::ShiftLeft(a, b) => {
                Bitvector32Term::ShiftLeft(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::ArithmeticShiftRight(a, b) => Bitvector32Term::ArithmeticShiftRight(
                Box::new(self.bits(a)),
                Box::new(self.bits(b)),
            ),
            Bitvector32Term::LogicalShiftRight(a, b) => {
                Bitvector32Term::LogicalShiftRight(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::BitwiseAnd(a, b) => {
                Bitvector32Term::BitwiseAnd(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::BitwiseOr(a, b) => {
                Bitvector32Term::BitwiseOr(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::BitwiseXor(a, b) => {
                Bitvector32Term::BitwiseXor(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64Add(a, b) => {
                Bitvector32Term::Int64Add(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64Subtract(a, b) => {
                Bitvector32Term::Int64Subtract(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64Multiply(a, b) => {
                Bitvector32Term::Int64Multiply(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64Divide(a, b) => {
                Bitvector32Term::Int64Divide(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64Remainder(a, b) => {
                Bitvector32Term::Int64Remainder(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64ShiftLeft(a, b) => {
                Bitvector32Term::Int64ShiftLeft(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64ArithmeticShiftRight(a, b) => {
                Bitvector32Term::Int64ArithmeticShiftRight(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            Bitvector32Term::Int64BitwiseAnd(a, b) => {
                Bitvector32Term::Int64BitwiseAnd(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64BitwiseOr(a, b) => {
                Bitvector32Term::Int64BitwiseOr(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::Int64BitwiseXor(a, b) => {
                Bitvector32Term::Int64BitwiseXor(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64Add(a, b) => {
                Bitvector32Term::UInt64Add(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64Subtract(a, b) => {
                Bitvector32Term::UInt64Subtract(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64Multiply(a, b) => {
                Bitvector32Term::UInt64Multiply(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64Divide(a, b) => {
                Bitvector32Term::UInt64Divide(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64Remainder(a, b) => {
                Bitvector32Term::UInt64Remainder(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64ShiftLeft(a, b) => {
                Bitvector32Term::UInt64ShiftLeft(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64LogicalShiftRight(a, b) => {
                Bitvector32Term::UInt64LogicalShiftRight(
                    Box::new(self.bits(a)),
                    Box::new(self.bits(b)),
                )
            }
            Bitvector32Term::UInt64BitwiseAnd(a, b) => {
                Bitvector32Term::UInt64BitwiseAnd(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64BitwiseOr(a, b) => {
                Bitvector32Term::UInt64BitwiseOr(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::UInt64BitwiseXor(a, b) => {
                Bitvector32Term::UInt64BitwiseXor(Box::new(self.bits(a)), Box::new(self.bits(b)))
            }
            Bitvector32Term::BitwiseNot(v) => Bitvector32Term::BitwiseNot(Box::new(self.bits(v))),
            Bitvector32Term::Int64From32(v) => Bitvector32Term::Int64From32(Box::new(self.bits(v))),
            Bitvector32Term::UInt64From32(v) => {
                Bitvector32Term::UInt64From32(Box::new(self.bits(v)))
            }
            Bitvector32Term::UInt32From64(v) => {
                Bitvector32Term::UInt32From64(Box::new(self.bits(v)))
            }
            Bitvector32Term::Int64FromUInt32(v) => {
                Bitvector32Term::Int64FromUInt32(Box::new(self.bits(v)))
            }
            Bitvector32Term::UInt64FromInt32(v) => {
                Bitvector32Term::UInt64FromInt32(Box::new(self.bits(v)))
            }
            Bitvector32Term::UInt64FromInt64(v) => {
                Bitvector32Term::UInt64FromInt64(Box::new(self.bits(v)))
            }
            Bitvector32Term::Int64BitwiseNot(v) => {
                Bitvector32Term::Int64BitwiseNot(Box::new(self.bits(v)))
            }
            Bitvector32Term::UInt64BitwiseNot(v) => {
                Bitvector32Term::UInt64BitwiseNot(Box::new(self.bits(v)))
            }
            Bitvector32Term::Float32Negate(v) => {
                Bitvector32Term::Float32Negate(Box::new(self.bits(v)))
            }
            Bitvector32Term::Float64Negate(v) => {
                Bitvector32Term::Float64Negate(Box::new(self.bits(v)))
            }
            Bitvector32Term::If {
                condition,
                then_term,
                else_term,
            } => {
                if let Some(conditions) = &mut self.collected_conditions {
                    conditions.push(condition.as_ref().clone());
                }
                let condition = self.condition(condition);
                if self.conditions.is_some()
                    && let ConditionTerm::Constant(value) = condition
                {
                    return self.bits(if value { then_term } else { else_term });
                }
                Bitvector32Term::If {
                    condition: Box::new(condition),
                    then_term: Box::new(self.bits(then_term)),
                    else_term: Box::new(self.bits(else_term)),
                }
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                accumulator,
                item,
                body,
            } => Bitvector32Term::RangeFold {
                start: Box::new(self.bits(start)),
                end: Box::new(self.bits(end)),
                initial: Box::new(self.bits(initial)),
                accumulator: *accumulator,
                item: *item,
                body: if self.conditions.is_some() {
                    body.clone()
                } else {
                    Box::new(self.bits(body))
                },
            },
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                Bitvector32Term::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments.iter().map(|a| self.bits(a)).collect(),
                }
            }
            Bitvector32Term::ClickFunctionApplication { name, arguments } => {
                Bitvector32Term::ClickFunctionApplication {
                    name: name.clone(),
                    arguments: arguments.iter().map(|a| self.argument(a)).collect(),
                }
            }
            Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
                Bitvector32Term::AlgebraicMatch {
                    scrutinee: Box::new(self.algebraic(scrutinee)),
                    arms: arms
                        .iter()
                        .map(|a| AlgebraicBitvectorMatchArm {
                            variant: a.variant.clone(),
                            bindings: a.bindings.clone(),
                            body: if self.conditions.is_some() {
                                a.body.clone()
                            } else {
                                self.bits(&a.body)
                            },
                        })
                        .collect(),
                }
            }
            Bitvector32Term::MemoryLoad(memory, pointer) => {
                Bitvector32Term::MemoryLoad(memory.clone(), Box::new(self.pointer(pointer)))
            }
            Bitvector32Term::PointerAddress(pointer) => {
                Bitvector32Term::PointerAddress(Box::new(self.pointer(pointer)))
            }
            Bitvector32Term::IntegerToMachine { value, destination } => {
                Bitvector32Term::IntegerToMachine {
                    value: self.integer_shared(value).into(),
                    destination: *destination,
                }
            }
            Bitvector32Term::Float32Binary {
                operator,
                left,
                right,
            } => Bitvector32Term::Float32Binary {
                operator: *operator,
                left: Box::new(self.bits(left)),
                right: Box::new(self.bits(right)),
            },
            Bitvector32Term::Float64Binary {
                operator,
                left,
                right,
            } => Bitvector32Term::Float64Binary {
                operator: *operator,
                left: Box::new(self.bits(left)),
                right: Box::new(self.bits(right)),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        AlgebraicSchemas, AlgebraicType, AlgebraicValueType, AlgebraicVariantType,
    };

    #[test]
    fn narrowing_rewrite_visits_scale_with_selected_expression() {
        let from = Bitvector32Term::Variable(Variable(91));
        let to = Bitvector32Term::Variable(Variable(92));
        let make = |value: &Bitvector32Term, size| {
            Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
                name: "many".into(),
                arguments: vec![
                    PureFunctionArgument::Value(CValue::UInt32(
                        Bitvector32Term::UInt32From64(Box::new(value.clone()))
                    ));
                    size
                ],
            })
        };
        for size in [16, 64, 256] {
            let mut rewrite = TermRewrite::for_bits(&from, &to);
            assert_eq!(rewrite.term(&make(&from, size)), make(&to, size));
            assert!(rewrite.changed);
            assert_eq!(rewrite.visits, 2 + 2 * size);
        }
    }

    #[test]
    fn conditional_reduction_work_scales_with_selected_expression() {
        let condition = ConditionTerm::Variable(Variable(51));
        let conditions = HashMap::from([(condition.clone(), true)]);
        for size in [16, 64, 256] {
            let input = Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
                name: "many".into(),
                arguments: vec![
                    PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::If {
                        condition: Box::new(condition.clone()),
                        then_term: Box::new(Bitvector32Term::Constant(7)),
                        else_term: Box::new(Bitvector32Term::Constant(0)),
                    },));
                    size
                ],
            });
            let expected = Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
                name: "many".into(),
                arguments: vec![
                    PureFunctionArgument::Value(CValue::Int32(
                        Bitvector32Term::Constant(7),
                    ));
                    size
                ],
            });
            let mut rewrite = TermRewrite::for_conditions(&conditions);
            assert_eq!(rewrite.term(&input), expected);
            assert_eq!(rewrite.visits, 2 + 3 * size);
        }
    }

    #[test]
    fn conditional_reduction_does_not_use_outer_facts_under_a_binder() {
        let variable = Variable(51);
        let condition = ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(Bitvector32Term::Constant(0)),
        );
        let conditions = HashMap::from([(condition.clone(), true)]);
        let input = Bitvector32Term::RangeFold {
            start: Box::new(Bitvector32Term::Constant(0)),
            end: Box::new(Bitvector32Term::Constant(2)),
            initial: Box::new(Bitvector32Term::Constant(0)),
            accumulator: Variable(52),
            item: variable,
            body: Box::new(Bitvector32Term::If {
                condition: Box::new(condition),
                then_term: Box::new(Bitvector32Term::Constant(7)),
                else_term: Box::new(Bitvector32Term::Constant(0)),
            }),
        };
        assert_eq!(TermRewrite::for_conditions(&conditions).bits(&input), input);
    }

    #[test]
    fn mixed_algebraic_rewrite_visits_scale_with_the_selected_expression() {
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Unit".into(),
            fields: vec![],
        }]
        .into();
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "Marker".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "Marker".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        };
        let from = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(Variable(51)),
        };
        let to = AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(Variable(52)),
        };
        for size in [16, 64, 256] {
            let argument = |value: &AlgebraicTerm| {
                PureFunctionArgument::Value(CValue::Int32(
                    Bitvector32Term::ClickFunctionApplication {
                        name: "observe".into(),
                        arguments: vec![PureFunctionArgument::Algebraic(value.clone())],
                    },
                ))
            };
            let input = Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
                name: "many".into(),
                arguments: vec![argument(&from); size],
            });
            let expected = Term::Bitvector32(Bitvector32Term::ClickFunctionApplication {
                name: "many".into(),
                arguments: vec![argument(&to); size],
            });
            let mut rewrite = TermRewrite::new(&from, &to);
            assert_eq!(rewrite.term(&input), expected);
            assert!(rewrite.changed);
            assert_eq!(rewrite.visits, 2 + 2 * size);
        }
    }

    #[test]
    fn integer_rewrite_preserves_shared_repeated_squaring() {
        for depth in [8, 16, 32, 64] {
            let mut expression = IntegerTerm::constant_i64(2);
            for _ in 0..depth {
                let child: SharedIntegerTerm = expression.into();
                expression = IntegerTerm::Multiply(child.clone(), child);
            }
            let input = Term::Integer(expression);
            let conditions = HashMap::new();
            let mut rewrite = TermRewrite::for_conditions(&conditions);
            let Term::Integer(output) = rewrite.term(&input) else {
                unreachable!()
            };
            assert_eq!(&Term::Integer(output.clone()), &input);
            let root: SharedIntegerTerm = output.into();
            let mut pending = vec![root];
            let mut seen = std::collections::BTreeSet::new();
            while let Some(node) = pending.pop() {
                if !seen.insert(node.id()) {
                    continue;
                }
                if let IntegerTerm::Multiply(left, right) = node.as_ref() {
                    pending.push(left.clone());
                    pending.push(right.clone());
                }
            }
            assert_eq!(seen.len(), depth + 1);
            assert!(rewrite.visits <= depth + 4);
        }
    }

    #[test]
    fn integer_to_machine_rewrite_descends_nested_math_payload() {
        let payload = SharedIntegerTerm::from(IntegerTerm::Machine(
            crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(880)),
            ),
        ));
        let input = Term::Bitvector32(Bitvector32Term::IntegerToMachine {
            value: payload,
            destination: crate::kernel::MachineIntegerType::UInt32,
        });
        let mut rewrite = TermRewrite::for_bits(
            &Bitvector32Term::Variable(Variable(880)),
            &Bitvector32Term::Variable(Variable(881)),
        );
        let output = rewrite.term(&input);
        assert!(
            matches!(output, Term::Bitvector32(Bitvector32Term::IntegerToMachine {
            destination: crate::kernel::MachineIntegerType::UInt32,
            ref value,
        }) if matches!(value.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(Variable(881))))
        );
    }
}
