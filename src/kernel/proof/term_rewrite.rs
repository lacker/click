//! Sort-preserving congruence and explicitly directed conditional reduction.
//! Memory snapshots are opaque: this walks the selected logical expression,
//! never a heap or an ambient proof state.
use crate::kernel::*;
use crate::kernel::{
    AlgebraicBitvectorMatchArm, AlgebraicResultMatchArm, AlgebraicTerm, AlgebraicTermNode,
    AlgebraicValue, PureFunctionArgument,
};
use std::collections::HashMap;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Default)]
struct RewriteScope {
    c: BTreeMap<Variable, Variable>,
    integer: BTreeMap<Variable, Variable>,
    algebraic: BTreeMap<Variable, Variable>,
}

#[derive(Clone, Copy)]
enum BindingCarrier {
    C,
    Integer,
    Algebraic,
}

/// A constructor field may carry either a scalar C term or a pointer.  Keep
/// that distinction while rewriting so a same-ID binding in another carrier
/// cannot be substituted accidentally.
#[derive(Clone)]
pub(crate) enum TypedCReplacement {
    Bitvector(Bitvector32Term),
    Pointer(Pointer),
}

struct TypedVariableReplacements<'a> {
    c: &'a BTreeMap<Variable, TypedCReplacement>,
    integer: &'a BTreeMap<Variable, IntegerTerm>,
    algebraic: &'a BTreeMap<Variable, AlgebraicTerm>,
}

enum ScopeChange {
    C(Variable, Option<Variable>),
    Integer(Variable, Option<Variable>),
    Algebraic(Variable, Option<Variable>),
}

// Fold scopes use the same carrier maps as match scopes.  This separate log
// records only the temporary fold changes, so restoring a fold cannot disturb
// an enclosing algebraic match's scope changes.
enum FoldScopeChange {
    C(Variable, Option<Variable>),
    Integer(Variable, Option<Variable>),
}

#[derive(Clone, Default)]
struct CarrierVariables {
    c: BTreeSet<Variable>,
    integer: BTreeSet<Variable>,
    algebraic: BTreeSet<Variable>,
    nodes: usize,
    charge_work: bool,
    budgeted: bool,
    work_exhausted: bool,
}

impl CarrierVariables {
    fn for_rewrite(budgeted: bool) -> Self {
        Self {
            charge_work: true,
            budgeted,
            ..Self::default()
        }
    }

    fn contains(&self, carrier: BindingCarrier, variable: Variable) -> bool {
        match carrier {
            BindingCarrier::C => self.c.contains(&variable),
            BindingCarrier::Integer => self.integer.contains(&variable),
            BindingCarrier::Algebraic => self.algebraic.contains(&variable),
        }
    }

    fn visit(&mut self) -> bool {
        if self.work_exhausted {
            return false;
        }
        self.nodes = self.nodes.saturating_add(1);
        if !self.charge_work {
            return true;
        }
        self.work_exhausted = if self.budgeted {
            crate::instrumentation::deadline_exceeded_with_work(1)
        } else {
            crate::instrumentation::record_deterministic_work(1);
            false
        };
        !self.work_exhausted
    }

    fn exhausted(&self) -> bool {
        self.work_exhausted
    }
}

fn c_value_variable(value: &CValue) -> Option<Variable> {
    match value {
        CValue::Bool(Bitvector32Term::Variable(variable))
        | CValue::Int16(Bitvector32Term::Variable(variable))
        | CValue::UInt8(Bitvector32Term::Variable(variable))
        | CValue::UInt16(Bitvector32Term::Variable(variable))
        | CValue::Int32(Bitvector32Term::Variable(variable))
        | CValue::UInt32(Bitvector32Term::Variable(variable))
        | CValue::Int64(Bitvector32Term::Variable(variable))
        | CValue::UInt64(Bitvector32Term::Variable(variable))
        | CValue::Float32(Bitvector32Term::Variable(variable))
        | CValue::Float64(Bitvector32Term::Variable(variable)) => Some(*variable),
        CValue::Pointer(pointer) => match &pointer.block {
            PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
                Some(*variable)
            }
            _ => None,
        },
        _ => None,
    }
}

fn typed_c_replacement(value: &CValue) -> Option<TypedCReplacement> {
    match value {
        CValue::Bool(term)
        | CValue::Int16(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::Int32(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => Some(TypedCReplacement::Bitvector(term.clone())),
        CValue::Pointer(pointer) => Some(TypedCReplacement::Pointer(pointer.pointer().clone())),
        CValue::Void => None,
    }
}

fn binding_variable(value: &AlgebraicValue) -> Option<(BindingCarrier, Variable)> {
    match value {
        AlgebraicValue::C(value) => {
            c_value_variable(value).map(|variable| (BindingCarrier::C, variable))
        }
        AlgebraicValue::Integer(IntegerTerm::Variable(variable)) => {
            Some((BindingCarrier::Integer, *variable))
        }
        AlgebraicValue::Algebraic(AlgebraicTerm {
            node: AlgebraicTermNode::Variable(variable),
            ..
        }) => Some((BindingCarrier::Algebraic, *variable)),
        _ => None,
    }
}

fn typed_binding_variable(
    expected: &AlgebraicValueType,
    binding: &AlgebraicValue,
) -> Option<(BindingCarrier, Variable)> {
    match (expected, binding) {
        (AlgebraicValueType::Integer, AlgebraicValue::Integer(IntegerTerm::Variable(variable))) => {
            Some((BindingCarrier::Integer, *variable))
        }
        (AlgebraicValueType::C(expected), AlgebraicValue::C(value))
            if value.c_type() == *expected =>
        {
            c_value_declaration_variable(value).map(|variable| (BindingCarrier::C, variable))
        }
        (
            AlgebraicValueType::Algebraic { .. } | AlgebraicValueType::Parameter(_),
            AlgebraicValue::Algebraic(value),
        ) if value.algebraic_type.value_type() == *expected
            && matches!(&value.node, AlgebraicTermNode::Variable(_)) =>
        {
            let AlgebraicTermNode::Variable(variable) = &value.node else {
                unreachable!()
            };
            Some((BindingCarrier::Algebraic, *variable))
        }
        _ => None,
    }
}

fn c_value_declaration_variable(value: &CValue) -> Option<Variable> {
    match value {
        CValue::Bool(Bitvector32Term::Variable(variable))
        | CValue::Int16(Bitvector32Term::Variable(variable))
        | CValue::UInt8(Bitvector32Term::Variable(variable))
        | CValue::UInt16(Bitvector32Term::Variable(variable))
        | CValue::Int32(Bitvector32Term::Variable(variable))
        | CValue::UInt32(Bitvector32Term::Variable(variable))
        | CValue::Int64(Bitvector32Term::Variable(variable))
        | CValue::UInt64(Bitvector32Term::Variable(variable))
        | CValue::Float32(Bitvector32Term::Variable(variable))
        | CValue::Float64(Bitvector32Term::Variable(variable)) => Some(*variable),
        CValue::Pointer(pointer)
            if matches!(
                &pointer.pointer().block,
                PointerBlock::Symbolic(_) | PointerBlock::FunctionSymbolic(_)
            ) && matches!(&pointer.pointer().offset, PointerOffsetTerm::Constant(0)) =>
        {
            match pointer.pointer().block {
                PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
                    Some(variable)
                }
                _ => unreachable!(),
            }
        }
        _ => None,
    }
}

fn replace_binding_variable(
    value: &mut AlgebraicValue,
    carrier: BindingCarrier,
    variable: Variable,
) {
    match (carrier, value) {
        (BindingCarrier::C, AlgebraicValue::C(value)) => match value {
            CValue::Bool(term)
            | CValue::Int16(term)
            | CValue::UInt8(term)
            | CValue::UInt16(term)
            | CValue::Int32(term)
            | CValue::UInt32(term)
            | CValue::Int64(term)
            | CValue::UInt64(term)
            | CValue::Float32(term)
            | CValue::Float64(term)
                if matches!(term, Bitvector32Term::Variable(_)) =>
            {
                *term = Bitvector32Term::Variable(variable);
            }
            CValue::Pointer(pointer)
                if matches!(
                    &pointer.block,
                    PointerBlock::Symbolic(_) | PointerBlock::FunctionSymbolic(_)
                ) =>
            {
                let mut replaced = pointer.pointer().clone();
                replaced.block = match replaced.block {
                    PointerBlock::FunctionSymbolic(_) => PointerBlock::FunctionSymbolic(variable),
                    _ => PointerBlock::Symbolic(variable),
                };
                pointer.replace_pointer(replaced);
            }
            _ => {}
        },
        (BindingCarrier::Integer, AlgebraicValue::Integer(term)) => {
            *term = IntegerTerm::Variable(variable);
        }
        (BindingCarrier::Algebraic, AlgebraicValue::Algebraic(term)) => {
            if matches!(&term.node, AlgebraicTermNode::Variable(_)) {
                term.node = AlgebraicTermNode::Variable(variable);
            }
        }
        _ => {}
    }
}

fn restore_mapping(
    mappings: &mut BTreeMap<Variable, Variable>,
    variable: Variable,
    previous: Option<Variable>,
) {
    if let Some(previous) = previous {
        mappings.insert(variable, previous);
    } else {
        mappings.remove(&variable);
    }
}

fn collect_integer_shared_carriers(
    term: &SharedIntegerTerm,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if seen.insert(term.id()) {
        collect_integer_carriers(term, variables, seen);
    }
}

fn collect_integer_carriers(
    term: &IntegerTerm,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match term {
        IntegerTerm::Constant(_) => {}
        IntegerTerm::Variable(variable) => {
            variables.integer.insert(*variable);
        }
        IntegerTerm::Machine(value) => collect_bitvector_carriers(value.value(), variables),
        IntegerTerm::Negate(value) => collect_integer_shared_carriers(value, variables, seen),
        IntegerTerm::Add(left, right)
        | IntegerTerm::Subtract(left, right)
        | IntegerTerm::Multiply(left, right) => {
            collect_integer_shared_carriers(left, variables, seen);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(right, variables, seen);
        }
        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        } => {
            match index {
                IntegerRangeFoldIndex::Int32 { start, end } => {
                    collect_bitvector_carriers(start.value(), variables);
                    if variables.exhausted() {
                        return;
                    }
                    collect_bitvector_carriers(end.value(), variables);
                }
                IntegerRangeFoldIndex::Integer { start, end } => {
                    collect_integer_shared_carriers(start, variables, seen);
                    if variables.exhausted() {
                        return;
                    }
                    collect_integer_shared_carriers(end, variables, seen);
                }
            }
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(initial, variables, seen);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(body, variables, seen);
            if variables.exhausted() {
                return;
            }
            variables.integer.insert(*accumulator);
            match index {
                IntegerRangeFoldIndex::Integer { .. } => {
                    variables.integer.insert(*item);
                }
                IntegerRangeFoldIndex::Int32 { .. } => {
                    variables.c.insert(*item);
                }
            }
        }
        IntegerTerm::PureFunctionApplication(application) => {
            for argument in application.arguments() {
                collect_argument_carriers(argument, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
            collect_algebraic_carriers_seen(scrutinee, variables, seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_carriers(binding, variables, seen);
                    if variables.exhausted() {
                        return;
                    }
                }
                collect_integer_shared_carriers(&arm.body, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
    }
}

fn collect_argument_carriers(
    argument: &PureFunctionArgument,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match argument {
        PureFunctionArgument::Value(value) => collect_c_value_carriers(value, variables),
        PureFunctionArgument::Integer(value) => {
            collect_integer_shared_carriers(value, variables, seen)
        }
        PureFunctionArgument::Algebraic(value) => {
            collect_algebraic_carriers_seen(value, variables, seen)
        }
        PureFunctionArgument::ArrayRef {
            memory: _, pointer, ..
        } => {
            collect_c_value_carriers(pointer, variables);
        }
    }
}

fn collect_algebraic_value_carriers(
    value: &AlgebraicValue,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match value {
        AlgebraicValue::C(value) => collect_c_value_carriers(value, variables),
        AlgebraicValue::Integer(value) => collect_integer_carriers(value, variables, seen),
        AlgebraicValue::Algebraic(value) => collect_algebraic_carriers_seen(value, variables, seen),
    }
}

fn collect_c_value_carriers(value: &CValue, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match value {
        CValue::Void => {}
        CValue::Bool(term)
        | CValue::Int16(term)
        | CValue::UInt8(term)
        | CValue::UInt16(term)
        | CValue::Int32(term)
        | CValue::UInt32(term)
        | CValue::Int64(term)
        | CValue::UInt64(term)
        | CValue::Float32(term)
        | CValue::Float64(term) => collect_bitvector_carriers(term, variables),
        CValue::Pointer(pointer) => collect_pointer_carriers(pointer, variables),
    }
}

fn collect_algebraic_carriers(term: &AlgebraicTerm, variables: &mut CarrierVariables) {
    collect_algebraic_carriers_seen(term, variables, &mut BTreeSet::new());
}

fn collect_algebraic_carriers_seen(
    term: &AlgebraicTerm,
    variables: &mut CarrierVariables,
    seen: &mut BTreeSet<u64>,
) {
    if !variables.visit() {
        return;
    }
    match &term.node {
        AlgebraicTermNode::Variable(variable) => {
            variables.algebraic.insert(*variable);
        }
        AlgebraicTermNode::Constructor { fields, .. } => {
            for field in fields {
                collect_algebraic_value_carriers(field, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::Match { scrutinee, arms } => {
            collect_algebraic_carriers_seen(scrutinee, variables, seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_carriers(binding, variables, seen);
                    if variables.exhausted() {
                        return;
                    }
                }
                collect_algebraic_carriers_seen(&arm.body, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        AlgebraicTermNode::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_argument_carriers(argument, variables, seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
    }
}

fn collect_pointer_carriers(pointer: &Pointer, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match &pointer.block {
        PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) => {
            variables.c.insert(*variable);
        }
        _ => {}
    }
    collect_pointer_offset_carriers(&pointer.offset, variables);
}

fn collect_condition_carriers(condition: &ConditionTerm, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match condition {
        ConditionTerm::AlgebraicEqual(left, right) => {
            let mut seen = BTreeSet::new();
            collect_algebraic_carriers_seen(left, variables, &mut seen);
            if variables.exhausted() {
                return;
            }
            collect_algebraic_carriers_seen(right, variables, &mut seen);
        }
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right) => {
            let mut seen = BTreeSet::new();
            collect_integer_shared_carriers(left, variables, &mut seen);
            if variables.exhausted() {
                return;
            }
            collect_integer_shared_carriers(right, variables, &mut seen);
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => {}
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64Equal(left, right)
        | ConditionTerm::Bitvector64SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector64SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector64SignedShiftLeftOverflows(left, right) => {
            collect_bitvector_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(right, variables);
        }
        ConditionTerm::Float32(float_condition) | ConditionTerm::Float64(float_condition) => {
            float_condition.for_each_bitvector_term(|term| {
                if !variables.exhausted() {
                    collect_bitvector_carriers(term, variables);
                }
            });
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_pointer_offset_carriers(right, variables);
        }
        ConditionTerm::PointerEqual(left, right) => {
            collect_pointer_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_pointer_carriers(right, variables);
        }
    }
}

fn collect_bitvector_carriers(term: &Bitvector32Term, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_) => {}
        Bitvector32Term::Variable(variable) => {
            variables.c.insert(*variable);
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::UnsignedDivide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::UnsignedRemainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::LogicalShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right)
        | Bitvector32Term::Int64Add(left, right)
        | Bitvector32Term::Int64Subtract(left, right)
        | Bitvector32Term::Int64Multiply(left, right)
        | Bitvector32Term::Int64Divide(left, right)
        | Bitvector32Term::Int64Remainder(left, right)
        | Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64Add(left, right)
        | Bitvector32Term::UInt64Subtract(left, right)
        | Bitvector32Term::UInt64Multiply(left, right)
        | Bitvector32Term::UInt64Divide(left, right)
        | Bitvector32Term::UInt64Remainder(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            collect_bitvector_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(right, variables);
        }
        Bitvector32Term::BitwiseNot(value)
        | Bitvector32Term::Int64BitwiseNot(value)
        | Bitvector32Term::UInt64BitwiseNot(value)
        | Bitvector32Term::Int64From32(value)
        | Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt32From64(value)
        | Bitvector32Term::Int64FromUInt32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value)
        | Bitvector32Term::Float32Negate(value)
        | Bitvector32Term::Float64Negate(value) => collect_bitvector_carriers(value, variables),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_carriers(condition, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(then_term, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(else_term, variables);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            collect_bitvector_carriers(start, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(end, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(initial, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(body, variables);
            if variables.exhausted() {
                return;
            }
            variables.c.insert(*accumulator);
            variables.c.insert(*item);
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
            for argument in arguments {
                collect_bitvector_carriers(argument, variables);
                if variables.exhausted() {
                    return;
                }
            }
        }
        Bitvector32Term::ClickFunctionApplication { arguments, .. } => {
            let mut seen = BTreeSet::new();
            for argument in arguments {
                collect_argument_carriers(argument, variables, &mut seen);
                if variables.exhausted() {
                    return;
                }
            }
        }
        Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
            let mut seen = BTreeSet::new();
            collect_algebraic_carriers_seen(scrutinee, variables, &mut seen);
            if variables.exhausted() {
                return;
            }
            for arm in arms {
                for binding in &arm.bindings {
                    collect_algebraic_value_carriers(binding, variables, &mut seen);
                    if variables.exhausted() {
                        return;
                    }
                }
                collect_bitvector_carriers(&arm.body, variables);
                if variables.exhausted() {
                    return;
                }
            }
        }
        // Memory snapshots are opaque proof-state values.  Only the selected
        // pointer expression participates in freshness collection.
        Bitvector32Term::MemoryLoad(_, pointer) => {
            collect_pointer_carriers(pointer, variables);
        }
        Bitvector32Term::PointerAddress(pointer) => {
            collect_pointer_carriers(pointer, variables);
        }
        Bitvector32Term::IntegerToMachine { value, .. } => {
            collect_integer_shared_carriers(value, variables, &mut BTreeSet::new());
        }
        Bitvector32Term::Float32Binary { left, right, .. }
        | Bitvector32Term::Float64Binary { left, right, .. } => {
            collect_bitvector_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_bitvector_carriers(right, variables);
        }
    }
}

fn collect_pointer_offset_carriers(offset: &PointerOffsetTerm, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match offset {
        PointerOffsetTerm::Constant(_) => {}
        PointerOffsetTerm::Variable(variable) => {
            variables.c.insert(*variable);
        }
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_pointer_offset_carriers(right, variables);
        }
        PointerOffsetTerm::Int32Scaled { value, .. }
        | PointerOffsetTerm::Int64Scaled { value, .. } => {
            collect_bitvector_carriers(value, variables)
        }
    }
}

fn collect_sequence_carriers(term: &SequenceTerm, variables: &mut CarrierVariables) {
    if !variables.visit() {
        return;
    }
    match term.node.as_ref() {
        SequenceTermNode::Literal(values) => {
            for value in values.iter() {
                collect_c_value_carriers(value, variables);
                if variables.exhausted() {
                    return;
                }
            }
        }
        SequenceTermNode::Concat(left, right) => {
            collect_sequence_carriers(left, variables);
            if variables.exhausted() {
                return;
            }
            collect_sequence_carriers(right, variables);
        }
    }
}

/// Collect variables needed for capture avoidance in the checked Integer
/// substitution fragment.  Pure function ArrayRef snapshots are proof-state
/// values, so their memory field is deliberately not traversed here; only the
/// explicit pointer expression participates in lexical freshness.
pub(crate) fn collect_integer_substitution_variables(
    proposition: &Proposition,
    variables: &mut BTreeSet<Variable>,
) {
    let mut carriers = CarrierVariables::default();
    match proposition {
        Proposition::Equal(left, right) => {
            collect_integer_substitution_term_variables(left, &mut carriers);
            collect_integer_substitution_term_variables(right, &mut carriers);
        }
        Proposition::ConditionIs(condition, _) => {
            collect_condition_carriers(condition, &mut carriers);
        }
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            collect_integer_substitution_variables(left, variables);
            collect_integer_substitution_variables(right, variables);
            return;
        }
        Proposition::Not(body) => {
            collect_integer_substitution_variables(body, variables);
            return;
        }
        Proposition::ForAll { body, .. } | Proposition::Exists { body, .. } => {
            collect_integer_substitution_variables(body, variables);
            return;
        }
        _ => return,
    }
    variables.extend(carriers.c);
    variables.extend(carriers.integer);
    variables.extend(carriers.algebraic);
}

fn collect_integer_substitution_term_variables(term: &Term, variables: &mut CarrierVariables) {
    match term {
        Term::Integer(value) => collect_integer_carriers(value, variables, &mut BTreeSet::new()),
        Term::Bitvector32(value) => collect_bitvector_carriers(value, variables),
        Term::CValue(value) => collect_c_value_carriers(value, variables),
        Term::Condition(value) => collect_condition_carriers(value, variables),
        Term::PointerOffset(value) => collect_pointer_offset_carriers(value, variables),
        Term::Algebraic(value) => collect_algebraic_carriers(value, variables),
        _ => {}
    }
}

// Once a checked rewrite runs out of work, its caller discards the result and
// reports the bounded failure.  Keep the transient value used to unwind the
// walker shallow; cloning an unvisited C/ADT subtree here would defeat the
// bound that caused the failure.
fn exhausted_algebraic(term: &AlgebraicTerm) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: term.algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(u64::MAX)),
    }
}

fn exhausted_integer(term: &IntegerTerm) -> IntegerTerm {
    match term {
        IntegerTerm::AlgebraicMatch { scrutinee, .. } => IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(exhausted_algebraic(scrutinee)),
            arms: Vec::new(),
        },
        IntegerTerm::Variable(variable) => IntegerTerm::Variable(*variable),
        _ => IntegerTerm::constant_i64(0),
    }
}

fn exhausted_pointer() -> Pointer {
    Pointer {
        block: PointerBlock::Concrete(String::new()),
        offset: PointerOffsetTerm::Constant(0),
    }
}

fn exhausted_offset() -> PointerOffsetTerm {
    PointerOffsetTerm::Constant(0)
}

fn exhausted_c_value(value: &CValue) -> CValue {
    match value {
        CValue::Void => CValue::Void,
        CValue::Bool(_) => CValue::Bool(Bitvector32Term::Constant(0)),
        CValue::Int16(_) => CValue::Int16(Bitvector32Term::Constant(0)),
        CValue::UInt8(_) => CValue::UInt8(Bitvector32Term::Constant(0)),
        CValue::UInt16(_) => CValue::UInt16(Bitvector32Term::Constant(0)),
        CValue::Int32(_) => CValue::Int32(Bitvector32Term::Constant(0)),
        CValue::UInt32(_) => CValue::UInt32(Bitvector32Term::Constant(0)),
        CValue::Int64(_) => CValue::Int64(Bitvector32Term::Constant(0)),
        CValue::UInt64(_) => CValue::UInt64(Bitvector32Term::Constant(0)),
        CValue::Float32(_) => CValue::Float32(Bitvector32Term::Constant(0)),
        CValue::Float64(_) => CValue::Float64(Bitvector32Term::Constant(0)),
        CValue::Pointer(pointer) => CValue::Pointer(
            CPointerValue::new(exhausted_pointer(), pointer.c_type())
                .with_pointee_volatile(pointer.pointee_volatile())
                .with_pointee_constant(pointer.pointee_constant()),
        ),
    }
}

fn exhausted_sequence(term: &SequenceTerm) -> SequenceTerm {
    SequenceTerm {
        element_type: term.element_type,
        node: std::sync::Arc::new(SequenceTermNode::Literal(Vec::<CValue>::new().into())),
    }
}

fn exhausted_argument(argument: &PureFunctionArgument) -> PureFunctionArgument {
    match argument {
        PureFunctionArgument::Value(value) => PureFunctionArgument::Value(exhausted_c_value(value)),
        PureFunctionArgument::Integer(value) => {
            PureFunctionArgument::Integer(exhausted_integer(value.as_ref()).into())
        }
        PureFunctionArgument::Algebraic(value) => {
            PureFunctionArgument::Algebraic(exhausted_algebraic(value))
        }
        PureFunctionArgument::ArrayRef {
            memory,
            pointer,
            element_type,
        } => PureFunctionArgument::ArrayRef {
            memory: memory.clone(),
            pointer: exhausted_c_value(pointer),
            element_type: *element_type,
        },
    }
}

fn exhausted_term(term: &Term) -> Term {
    match term {
        Term::Condition(_) => Term::Condition(ConditionTerm::Constant(false)),
        Term::Bitvector32(_) => Term::Bitvector32(Bitvector32Term::Constant(0)),
        Term::Integer(value) => Term::Integer(exhausted_integer(value)),
        Term::PointerOffset(_) => Term::PointerOffset(exhausted_offset()),
        Term::CValue(value) => Term::CValue(exhausted_c_value(value)),
        Term::Sequence(value) => Term::Sequence(exhausted_sequence(value)),
        Term::Algebraic(value) => Term::Algebraic(exhausted_algebraic(value)),
        _ => term.clone(),
    }
}

fn exhausted_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(false), true)
}

struct IntegerVariableRewrite<'a> {
    from: Variable,
    to: &'a IntegerTerm,
    renamings: &'a BTreeMap<Variable, Variable>,
}

/// Saved lexical state for the checked pure-Integer substitution walker.
///
/// Pure proposition substitution traverses the proposition itself because the
/// general proposition walker deliberately does not rewrite binder-bearing
/// propositions.  Keeping the scope token here lets that traversal install
/// the same carrier-aware mapping in one `TermRewrite` instance and restore it
/// on every return path without cloning a suffix environment.
pub(crate) struct IntegerSubstitutionScope {
    variable: Variable,
    previous: Option<Variable>,
    scope_id: u64,
    integer_shadowed: bool,
}

pub(crate) struct TermRewrite<'a> {
    algebraic: Option<(&'a AlgebraicTerm, &'a AlgebraicTerm)>,
    bitvector: Option<(&'a Bitvector32Term, &'a Bitvector32Term)>,
    pointer_variable: Option<(Variable, &'a Pointer)>,
    conditions: Option<&'a HashMap<ConditionTerm, bool>>,
    collected_conditions: Option<Vec<ConditionTerm>>,
    integer_cache: HashMap<(u64, u64), IntegerTerm>,
    scope_renaming_max: u64,
    integer_body_summaries: HashMap<u64, crate::kernel::prelude::IntegerScopeSummary>,
    integer_variables: Option<IntegerVariableRewrite<'a>>,
    integer_replacement_variables: Option<BTreeSet<Variable>>,
    bitvector_replacement_variables: Option<BTreeSet<Variable>>,
    integer_replacement_variable_max: Option<u64>,
    bitvector_replacement_variable_max: Option<u64>,
    integer_renaming_max: Option<u64>,
    enforce_integer_work_limit: bool,
    typed_variables: Option<TypedVariableReplacements<'a>>,
    integer_shadowed: bool,
    scope: RewriteScope,
    scope_id: u64,
    next_scope_id: u64,
    source_disabled: bool,
    source_variables_reserved: bool,
    reserved_variables: BTreeSet<Variable>,
    fresh_next: u64,
    replacement_carriers: Option<CarrierVariables>,
    pub(crate) unsupported_integer_scope: bool,
    pub(crate) integer_work_exhausted: bool,
    pub(crate) changed: bool,
    #[cfg(test)]
    pub(crate) visits: usize,
    #[cfg(test)]
    pub(crate) collector_visits: usize,
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
            scope_renaming_max: 0,
            integer_body_summaries: HashMap::new(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            unsupported_integer_scope: false,
            integer_work_exhausted: false,
            pointer_variable: None,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        }
    }
    pub(crate) fn for_bits(from: &'a Bitvector32Term, to: &'a Bitvector32Term) -> Self {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        let mut integer_replacement_variables = BTreeSet::new();
        crate::kernel::prelude::collect_bitvector_integer_variables(
            to,
            &mut integer_replacement_variables,
        );
        let mut bitvector_replacement_variables = BTreeSet::new();
        crate::kernel::prelude::collect_bitvector_capture_variables(
            to,
            &mut bitvector_replacement_variables,
        );
        let mut replacement_integer_binders = BTreeSet::new();
        let mut replacement_bitvector_binders = BTreeSet::new();
        crate::kernel::prelude::collect_bitvector_binder_variables(
            to,
            &mut replacement_integer_binders,
            &mut replacement_bitvector_binders,
        );
        let integer_replacement_variable_max = integer_replacement_variables
            .iter()
            .chain(replacement_integer_binders.iter())
            .map(|variable| variable.0)
            .max();
        let bitvector_replacement_variable_max = bitvector_replacement_variables
            .iter()
            .chain(replacement_bitvector_binders.iter())
            .map(|variable| variable.0)
            .max();
        let mut rewrite = Self {
            conditions: None,
            collected_conditions: None,
            algebraic: None,
            bitvector: Some((from, to)),
            changed: false,
            integer_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: HashMap::new(),
            integer_replacement_variables: Some(integer_replacement_variables),
            bitvector_replacement_variables: Some(bitvector_replacement_variables),
            integer_replacement_variable_max,
            bitvector_replacement_variable_max,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            unsupported_integer_scope: false,
            integer_work_exhausted: false,
            pointer_variable: None,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        };
        rewrite.seed_fresh_allocator();
        rewrite
    }

    /// Construct the checked machine rewrite used by range-fold laws. Setup
    /// collection and the subsequent traversal share the tactic's bounded
    /// work state, so a partial term is never accepted as a checked result.
    pub(crate) fn for_bits_checked(from: &'a Bitvector32Term, to: &'a Bitvector32Term) -> Self {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        let mut rewrite = Self::for_bits(from, to);
        rewrite.enforce_integer_work_limit = true;
        rewrite.integer_work_exhausted |= crate::instrumentation::checked_collection_exhausted();
        rewrite
    }

    pub(crate) fn for_conditions(conditions: &'a HashMap<ConditionTerm, bool>) -> Self {
        Self {
            algebraic: None,
            bitvector: None,
            conditions: Some(conditions),
            collected_conditions: None,
            changed: false,
            integer_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: HashMap::new(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            unsupported_integer_scope: false,
            integer_work_exhausted: false,
            pointer_variable: None,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
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
            scope_renaming_max: 0,
            integer_body_summaries: HashMap::new(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            unsupported_integer_scope: false,
            integer_work_exhausted: false,
            changed: false,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        }
    }

    /// Maps Integer variables in one binder-free atomic proposition. The
    /// caller handles logical binders and reserves the replacement's variables.
    /// Unsupported internal scopes are reported, never silently copied.
    pub(crate) fn for_integer_variables(
        from: Variable,
        to: &'a IntegerTerm,
        shadowed: bool,
        renamings: &'a BTreeMap<Variable, Variable>,
    ) -> Self {
        let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
        let mut replacement_integer_binders = BTreeSet::new();
        let mut replacement_bitvector_binders = BTreeSet::new();
        crate::kernel::prelude::collect_integer_binder_variables(
            to,
            &mut replacement_integer_binders,
            &mut replacement_bitvector_binders,
        );
        let mut integer_replacement_variables = BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(
            to,
            &mut integer_replacement_variables,
        );
        let mut bitvector_replacement_variables = BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(
            to,
            &mut bitvector_replacement_variables,
        );
        let integer_replacement_variable_max = integer_replacement_variables
            .iter()
            .chain(replacement_integer_binders.iter())
            .map(|variable| variable.0)
            .max();
        let bitvector_replacement_variable_max = bitvector_replacement_variables
            .iter()
            .chain(replacement_bitvector_binders.iter())
            .map(|variable| variable.0)
            .max();
        let integer_renaming_max = renamings.values().map(|variable| variable.0).max();
        let mut walker = Self {
            algebraic: None,
            bitvector: None,
            pointer_variable: None,
            conditions: None,
            collected_conditions: None,
            integer_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: HashMap::new(),
            integer_replacement_variables: Some(integer_replacement_variables),
            bitvector_replacement_variables: Some(bitvector_replacement_variables),
            integer_replacement_variable_max,
            bitvector_replacement_variable_max,
            integer_renaming_max,
            enforce_integer_work_limit: true,
            integer_variables: None,
            typed_variables: None,
            integer_shadowed: shadowed,
            scope: RewriteScope {
                integer: renamings.clone(),
                ..RewriteScope::default()
            },
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            unsupported_integer_scope: false,
            integer_work_exhausted: false,
            changed: false,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        };
        walker.integer_variables = Some(IntegerVariableRewrite {
            from,
            to,
            renamings,
        });
        walker.seed_fresh_allocator();
        walker.integer_work_exhausted |= crate::instrumentation::checked_collection_exhausted();
        walker
    }

    /// Reserve all IDs collected by the outer pure-proposition validation in
    /// one pass.  The ordinary term entry points collect their source terms
    /// lazily; checked pure substitution has already validated the complete
    /// proposition and must therefore avoid repeating that collection for
    /// every atomic leaf.
    pub(crate) fn reserve_integer_substitution_variables(
        &mut self,
        variables: &BTreeSet<Variable>,
    ) {
        if self.source_variables_reserved {
            return;
        }
        self.source_variables_reserved = true;
        self.charge_rewrite_work(1);
        if self.integer_work_exhausted {
            return;
        }
        // All collected IDs are reserved by starting the shared allocator
        // strictly above the maximum.  Keeping the complete source set in
        // `reserved_variables` would add an uncharged linear copy here and
        // would not change any allocation decision.
        if let Some(last) = variables.iter().next_back() {
            let Some(next) = last.0.checked_add(1) else {
                self.integer_work_exhausted = true;
                return;
            };
            self.fresh_next = self.fresh_next.max(next);
        }
    }

    /// Allocate a fresh Integer binder from the walker's shared allocator.
    /// The caller translates `None` into its checked substitution error after
    /// inspecting `integer_work_exhausted`.
    pub(crate) fn fresh_integer_substitution_variable(&mut self) -> Option<Variable> {
        self.fresh_variable()
    }

    /// Install an Integer binder mapping for a pure-proposition scope.  The
    /// map is carrier-specific, so a C binder with the same numeric ID cannot
    /// affect this scope.  Scope IDs invalidate the DAG cache whenever the
    /// visible mapping changes.
    pub(crate) fn push_integer_substitution_scope(
        &mut self,
        variable: Variable,
        mapped: Variable,
        integer_shadowed: bool,
    ) -> IntegerSubstitutionScope {
        let previous = self.scope.integer.insert(variable, mapped);
        let scope_id = self.scope_id;
        let previous_shadowed = self.integer_shadowed;
        if previous != Some(mapped) || previous_shadowed != integer_shadowed {
            self.bump_scope_id();
        }
        self.integer_shadowed = integer_shadowed;
        IntegerSubstitutionScope {
            variable,
            previous,
            scope_id,
            integer_shadowed: previous_shadowed,
        }
    }

    /// Restore a scope installed by `push_integer_substitution_scope`.
    pub(crate) fn pop_integer_substitution_scope(&mut self, scope: IntegerSubstitutionScope) {
        restore_mapping(&mut self.scope.integer, scope.variable, scope.previous);
        self.scope_id = scope.scope_id;
        self.integer_shadowed = scope.integer_shadowed;
    }

    /// Rewrites a constructor body with all field substitutions installed at
    /// once.  The replacement terms are inserted unchanged, so a field that
    /// mentions another binder is not rewritten by the later field mapping.
    pub(crate) fn for_typed_variables(
        c: &'a BTreeMap<Variable, TypedCReplacement>,
        integer: &'a BTreeMap<Variable, IntegerTerm>,
        algebraic: &'a BTreeMap<Variable, AlgebraicTerm>,
    ) -> Self {
        Self {
            algebraic: None,
            bitvector: None,
            pointer_variable: None,
            conditions: None,
            collected_conditions: None,
            integer_cache: HashMap::new(),
            scope_renaming_max: 0,
            integer_body_summaries: HashMap::new(),
            integer_replacement_variables: None,
            bitvector_replacement_variables: None,
            integer_replacement_variable_max: None,
            bitvector_replacement_variable_max: None,
            integer_renaming_max: None,
            enforce_integer_work_limit: false,
            integer_variables: None,
            typed_variables: Some(TypedVariableReplacements {
                c,
                integer,
                algebraic,
            }),
            integer_shadowed: false,
            scope: RewriteScope::default(),
            scope_id: 0,
            next_scope_id: 1,
            source_disabled: false,
            source_variables_reserved: false,
            reserved_variables: BTreeSet::new(),
            fresh_next: 0,
            replacement_carriers: None,
            unsupported_integer_scope: false,
            integer_work_exhausted: false,
            changed: false,
            #[cfg(test)]
            visits: 0,
            #[cfg(test)]
            collector_visits: 0,
        }
    }

    pub(crate) fn conditional_guards(proposition: &Proposition) -> Vec<ConditionTerm> {
        let empty = HashMap::new();
        let mut walker = TermRewrite::for_conditions(&empty);
        walker.collected_conditions = Some(Vec::new());
        walker.proposition(proposition);
        walker.collected_conditions.unwrap()
    }

    fn new_carrier_variables(&self) -> CarrierVariables {
        CarrierVariables::for_rewrite(
            self.integer_variables.is_some()
                || self.typed_variables.is_some()
                || self.enforce_integer_work_limit,
        )
    }

    fn checked_work_exhausted(&self) -> bool {
        self.integer_work_exhausted
    }

    fn seed_fresh_allocator(&mut self) {
        for variable in self
            .integer_replacement_variables
            .iter()
            .flat_map(|variables| variables.iter())
            .chain(
                self.bitvector_replacement_variables
                    .iter()
                    .flat_map(|variables| variables.iter()),
            )
        {
            self.reserved_variables.insert(*variable);
        }
        let upper = self
            .integer_replacement_variable_max
            .into_iter()
            .chain(self.bitvector_replacement_variable_max)
            .chain(self.integer_renaming_max)
            .max();
        if let Some(upper) = upper {
            self.fresh_next = self.fresh_next.max(upper.saturating_add(1));
        }
    }

    fn body_variable_max(&mut self, body: &SharedIntegerTerm) -> u64 {
        let body_id = body.id();
        if !self.integer_body_summaries.contains_key(&body_id) {
            let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
            crate::kernel::prelude::collect_integer_scope_summaries(
                body,
                &mut self.integer_body_summaries,
            );
            if crate::instrumentation::checked_collection_exhausted() {
                self.integer_work_exhausted = true;
                return 0;
            }
        }
        self.integer_body_summaries
            .get(&body_id)
            .map_or(0, |summary| summary.max)
    }

    fn remove_fold_scope_mapping(
        &mut self,
        integer: bool,
        variable: Variable,
        changes: &mut Vec<FoldScopeChange>,
    ) {
        let previous = if integer {
            self.scope.integer.remove(&variable)
        } else {
            self.scope.c.remove(&variable)
        };
        changes.push(if integer {
            FoldScopeChange::Integer(variable, previous)
        } else {
            FoldScopeChange::C(variable, previous)
        });
    }

    fn push_fold_scope_mapping(
        &mut self,
        integer: bool,
        from: Variable,
        to: Variable,
        changes: &mut Vec<FoldScopeChange>,
    ) {
        let previous = if integer {
            self.scope.integer.insert(from, to)
        } else {
            self.scope.c.insert(from, to)
        };
        changes.push(if integer {
            FoldScopeChange::Integer(from, previous)
        } else {
            FoldScopeChange::C(from, previous)
        });
        self.scope_renaming_max = self.scope_renaming_max.max(to.0);
    }

    fn restore_fold_scope_mappings(&mut self, changes: &[FoldScopeChange]) {
        for change in changes.iter().rev() {
            match change {
                FoldScopeChange::Integer(variable, previous) => {
                    restore_mapping(&mut self.scope.integer, *variable, *previous);
                }
                FoldScopeChange::C(variable, previous) => {
                    restore_mapping(&mut self.scope.c, *variable, *previous);
                }
            }
        }
    }

    fn reserve_source_variables(&mut self, variables: CarrierVariables) {
        if self.source_variables_reserved {
            return;
        }
        #[cfg(test)]
        {
            self.collector_visits = self.collector_visits.saturating_add(variables.nodes);
        }
        self.source_variables_reserved = true;
        self.integer_work_exhausted |= variables.work_exhausted;
        if self.integer_work_exhausted {
            return;
        }
        self.charge_rewrite_work(1);
        if self.integer_work_exhausted {
            return;
        }
        self.extend_reserved_variables(&variables);
    }

    fn extend_reserved_variables(&mut self, variables: &CarrierVariables) {
        for variable in variables
            .c
            .iter()
            .chain(variables.integer.iter())
            .chain(variables.algebraic.iter())
            .copied()
        {
            self.reserved_variables.insert(variable);
            if let Some(next) = variable.0.checked_add(1) {
                self.fresh_next = self.fresh_next.max(next);
            }
        }
    }

    fn reserve_terms_variables_once(&mut self, terms: &[&Term]) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        for term in terms {
            match term {
                Term::Condition(condition) => collect_condition_carriers(condition, &mut variables),
                Term::Bitvector32(value) => collect_bitvector_carriers(value, &mut variables),
                Term::Integer(value) => collect_integer_shared_carriers(
                    &SharedIntegerTerm::from((*value).clone()),
                    &mut variables,
                    &mut seen,
                ),
                Term::PointerOffset(offset) => {
                    collect_pointer_offset_carriers(offset, &mut variables)
                }
                Term::CValue(value) => collect_c_value_carriers(value, &mut variables),
                Term::Sequence(value) => collect_sequence_carriers(value, &mut variables),
                Term::Algebraic(value) => {
                    collect_algebraic_carriers_seen(value, &mut variables, &mut seen)
                }
                Term::CExpressionOutcome(_)
                | Term::CStatementOutcome(_)
                | Term::CFunctionOutcome(_)
                | Term::CMemory(_)
                | Term::CState(_) => {}
            }
            if variables.exhausted() {
                break;
            }
        }
        self.reserve_source_variables(variables);
    }

    fn reserve_term_variables_once(&mut self, term: &Term) {
        self.reserve_terms_variables_once(std::slice::from_ref(&term));
    }

    fn reserve_integer_variables_once(&mut self, term: &IntegerTerm) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_integer_shared_carriers(
            &SharedIntegerTerm::from(term.clone()),
            &mut variables,
            &mut BTreeSet::new(),
        );
        self.reserve_source_variables(variables);
    }

    fn reserve_bitvector_variables_once(&mut self, term: &Bitvector32Term) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_bitvector_carriers(term, &mut variables);
        self.reserve_source_variables(variables);
    }

    fn reserve_condition_variables_once(&mut self, condition: &ConditionTerm) {
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_condition_carriers(condition, &mut variables);
        self.reserve_source_variables(variables);
    }

    pub(crate) fn proposition(&mut self, proposition: &Proposition) -> Proposition {
        if self.checked_work_exhausted() {
            return exhausted_proposition();
        }
        if self.integer_variables.is_some()
            || self.typed_variables.is_some()
            || self.enforce_integer_work_limit
        {
            self.visit();
            if self.checked_work_exhausted() {
                return exhausted_proposition();
            }
        }
        match proposition {
            Proposition::Equal(a, b) => {
                self.reserve_terms_variables_once(&[a, b]);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                let left = self.term(a);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                let right = self.term(b);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                Proposition::Equal(left, right)
            }
            Proposition::ConditionIs(c, value) => {
                self.reserve_condition_variables_once(c);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                let condition = self.condition(c);
                if self.checked_work_exhausted() {
                    return exhausted_proposition();
                }
                Proposition::ConditionIs(condition, *value)
            }
            Proposition::Not(p) => {
                let body = self.proposition(p);
                if self.checked_work_exhausted() {
                    exhausted_proposition()
                } else {
                    Proposition::Not(Box::new(body))
                }
            }
            // Binder-bearing and compound propositions require their own explicit proof steps.
            _ => {
                if self.integer_variables.is_some()
                    || self.typed_variables.is_some()
                    || self.enforce_integer_work_limit
                {
                    self.integer_work_exhausted = true;
                    exhausted_proposition()
                } else {
                    proposition.clone()
                }
            }
        }
    }
    fn visit(&mut self) {
        if self.integer_variables.is_some()
            || self.typed_variables.is_some()
            || self.enforce_integer_work_limit
        {
            self.integer_work_exhausted |= crate::instrumentation::deadline_exceeded_with_work(1);
        } else {
            crate::instrumentation::record_deterministic_work(1);
        }
        #[cfg(test)]
        {
            self.visits += 1;
        }
    }
    pub(crate) fn term(&mut self, term: &Term) -> Term {
        self.reserve_term_variables_once(term);
        if self.checked_work_exhausted() {
            return exhausted_term(term);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_term(term);
        }
        let result = match term {
            Term::Algebraic(v) => Term::Algebraic(self.algebraic(v)),
            Term::Bitvector32(v) => Term::Bitvector32(self.bits(v)),
            Term::Integer(v) => Term::Integer(self.integer(v)),
            Term::CValue(v) => Term::CValue(self.value(v)),
            Term::Condition(v) => Term::Condition(self.condition(v)),
            Term::PointerOffset(v) => Term::PointerOffset(self.offset(v)),
            _ => term.clone(),
        };
        if self.checked_work_exhausted() {
            exhausted_term(term)
        } else {
            result
        }
    }
    fn algebraic(&mut self, term: &AlgebraicTerm) -> AlgebraicTerm {
        if self.checked_work_exhausted() {
            return exhausted_algebraic(term);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_algebraic(term);
        }
        if let AlgebraicTermNode::Variable(variable) = &term.node
            && let Some(mapped) = self.scope.algebraic.get(variable)
        {
            let mut result = term.clone();
            result.node = AlgebraicTermNode::Variable(*mapped);
            return result;
        }
        if let AlgebraicTermNode::Variable(variable) = &term.node
            && let Some(replacements) = &self.typed_variables
            && let Some(replacement) = replacements.algebraic.get(variable)
        {
            self.changed = true;
            return replacement.clone();
        }
        if let Some((from, to)) = self.algebraic
            && !self.source_disabled
            && term == from
        {
            self.changed = true;
            return self.rewrite_algebraic_replacement(to);
        }
        let node = match &term.node {
            AlgebraicTermNode::Variable(v) => AlgebraicTermNode::Variable(*v),
            AlgebraicTermNode::Constructor { variant, fields } => {
                let mut rewritten = Vec::with_capacity(fields.len());
                for field in fields {
                    rewritten.push(self.field(field));
                    if self.checked_work_exhausted() {
                        return exhausted_algebraic(term);
                    }
                }
                AlgebraicTermNode::Constructor {
                    variant: variant.clone(),
                    fields: rewritten,
                }
            }
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                let mut rewritten = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    rewritten.push(self.argument(argument));
                    if self.checked_work_exhausted() {
                        return exhausted_algebraic(term);
                    }
                }
                AlgebraicTermNode::PureFunctionApplication {
                    name: name.clone(),
                    arguments: rewritten,
                }
            }
            AlgebraicTermNode::Match { scrutinee, arms } => {
                self.reserve_algebraic_match_variables(term, scrutinee, arms);
                if self.checked_work_exhausted() {
                    return exhausted_algebraic(term);
                }
                let scrutinee = self.algebraic(scrutinee);
                if self.checked_work_exhausted() {
                    return exhausted_algebraic(term);
                }
                let mut rewritten_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let saved_scope_id = self.scope_id;
                    let saved_shadowed = self.integer_shadowed;
                    let mut changes = Vec::new();
                    let mut bindings = arm.bindings.clone();
                    if !self.rewrite_match_bindings(&mut bindings, &mut changes) {
                        self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                        self.integer_work_exhausted = true;
                        return exhausted_algebraic(term);
                    }
                    let body = if self.conditions.is_some() {
                        arm.body.clone()
                    } else {
                        self.algebraic(&arm.body)
                    };
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    if self.checked_work_exhausted() {
                        return exhausted_algebraic(term);
                    }
                    rewritten_arms.push(AlgebraicResultMatchArm {
                        variant: arm.variant.clone(),
                        bindings,
                        body,
                    });
                }
                AlgebraicTermNode::Match {
                    scrutinee: Box::new(scrutinee),
                    arms: rewritten_arms,
                }
            }
        };
        AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node,
        }
    }

    /// A replacement is an expression from the enclosing lexical scope.  It
    /// is inserted as-is: applying the current arm's renamings to it would
    /// capture a free variable in the replacement.
    fn rewrite_algebraic_replacement(&mut self, replacement: &AlgebraicTerm) -> AlgebraicTerm {
        replacement.clone()
    }
    fn field(&mut self, v: &AlgebraicValue) -> AlgebraicValue {
        if self.checked_work_exhausted() {
            return match v {
                AlgebraicValue::C(value) => AlgebraicValue::C(exhausted_c_value(value)),
                AlgebraicValue::Integer(value) => AlgebraicValue::Integer(exhausted_integer(value)),
                AlgebraicValue::Algebraic(value) => {
                    AlgebraicValue::Algebraic(exhausted_algebraic(value))
                }
            };
        }
        match v {
            AlgebraicValue::C(v) => AlgebraicValue::C(self.value(v)),
            AlgebraicValue::Integer(v) => AlgebraicValue::Integer(self.integer(v)),
            AlgebraicValue::Algebraic(v) => AlgebraicValue::Algebraic(self.algebraic(v)),
        }
    }
    fn argument(&mut self, a: &PureFunctionArgument) -> PureFunctionArgument {
        if self.checked_work_exhausted() {
            return exhausted_argument(a);
        }
        let result = match a {
            PureFunctionArgument::Value(v) => PureFunctionArgument::Value(self.value(v)),
            PureFunctionArgument::Integer(v) => {
                PureFunctionArgument::Integer(self.integer_shared(v).into())
            }
            PureFunctionArgument::Algebraic(v) => {
                PureFunctionArgument::Algebraic(self.algebraic(v))
            }
            PureFunctionArgument::ArrayRef {
                memory,
                pointer,
                element_type,
            } => PureFunctionArgument::ArrayRef {
                // A captured memory snapshot is an opaque proof-state value.
                // Rewrite only the explicit pointer argument; scanning or
                // rebuilding the snapshot would make substitution depend on
                // unrelated heap size.
                memory: memory.clone(),
                pointer: self.value(pointer),
                element_type: *element_type,
            },
        };
        if self.checked_work_exhausted() {
            exhausted_argument(a)
        } else {
            result
        }
    }
    fn value(&mut self, v: &CValue) -> CValue {
        if self.checked_work_exhausted() {
            return exhausted_c_value(v);
        }
        let result = match v {
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
        };
        if self.checked_work_exhausted() {
            exhausted_c_value(v)
        } else {
            result
        }
    }
    fn integer(&mut self, v: &IntegerTerm) -> IntegerTerm {
        self.reserve_integer_variables_once(v);
        if self.checked_work_exhausted() {
            return exhausted_integer(v);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_integer(v);
        }
        self.integer_shared(&SharedIntegerTerm::from(v.clone()))
    }
    fn integer_shared(&mut self, shared: &SharedIntegerTerm) -> IntegerTerm {
        if self.checked_work_exhausted() {
            return exhausted_integer(shared.as_ref());
        }
        let cache_key = (shared.id(), self.scope_key());
        if let Some(result) = self.integer_cache.get(&cache_key) {
            return result.clone();
        }
        self.visit();
        if self.checked_work_exhausted() {
            return exhausted_integer(shared.as_ref());
        }
        let result = match shared.as_ref() {
            IntegerTerm::Constant(value) => {
                if self.integer_variables.is_some()
                    || self.typed_variables.is_some()
                    || self.enforce_integer_work_limit
                {
                    self.integer_work_exhausted |=
                        crate::instrumentation::deadline_exceeded_with_work(
                            value.bits() as usize + 1,
                        );
                    if self.integer_work_exhausted {
                        return exhausted_integer(shared.as_ref());
                    }
                }
                shared.as_ref().clone()
            }
            IntegerTerm::Variable(variable) => self.rewrite_integer_variable(*variable),
            IntegerTerm::PureFunctionApplication(application) => {
                let mut arguments = Vec::with_capacity(application.arguments().len());
                for argument in application.arguments() {
                    arguments.push(self.argument(argument));
                    if self.checked_work_exhausted() {
                        return exhausted_integer(shared.as_ref());
                    }
                }
                IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    application.name().to_string(),
                    arguments,
                ))
            }
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
            IntegerTerm::RangeFold {
                index,
                initial,
                accumulator,
                item,
                body,
            } => self.rewrite_integer_range_fold(index, initial, *accumulator, *item, body),
            IntegerTerm::AlgebraicMatch { scrutinee, arms } => {
                self.rewrite_integer_match(scrutinee, arms)
            }
        };
        if self.checked_work_exhausted() {
            return exhausted_integer(shared.as_ref());
        }
        self.integer_cache.insert(cache_key, result.clone());
        result
    }

    fn rewrite_integer_range_fold(
        &mut self,
        index: &IntegerRangeFoldIndex,
        initial: &SharedIntegerTerm,
        original_accumulator: Variable,
        original_item: Variable,
        body: &SharedIntegerTerm,
    ) -> IntegerTerm {
        let item_is_integer = matches!(index, IntegerRangeFoldIndex::Integer { .. });
        if !item_is_integer && self.has_composite_bitvector_source() {
            // A composite source can contain variables whose binding status
            // changes under this C-item binder.  Refuse that scope until a
            // carrier-aware source summary is available; plain variable
            // sources remain fully supported.
            self.unsupported_integer_scope = true;
            return IntegerTerm::constant_i64(0);
        }
        let integer_source = self.integer_variables.as_ref().map(|mapping| mapping.from);
        let c_source = self.bitvector.and_then(|(from, _)| match from {
            Bitvector32Term::Variable(variable) => Some(*variable),
            _ => None,
        });

        // Typed substitutions use the same carrier-aware replacement summary
        // as algebraic matches.  In particular, a C variable with the same
        // numeric ID as an Integer variable must not affect this decision.
        if self.typed_variables.is_some() {
            self.ensure_replacement_carriers();
        }
        if self.checked_work_exhausted() {
            return IntegerTerm::constant_i64(0);
        }
        let integer_replacement_contains = self
            .integer_replacement_variables
            .as_ref()
            .is_some_and(|variables| variables.contains(&original_accumulator));
        let c_replacement_contains = self
            .bitvector_replacement_variables
            .as_ref()
            .is_some_and(|variables| variables.contains(&original_item));
        let typed_integer_replacement_contains = self
            .replacement_carriers
            .as_ref()
            .is_some_and(|variables| variables.integer.contains(&original_accumulator));
        let typed_integer_item_replacement_contains = self
            .replacement_carriers
            .as_ref()
            .is_some_and(|variables| variables.integer.contains(&original_item));
        let typed_c_replacement_contains = self
            .replacement_carriers
            .as_ref()
            .is_some_and(|variables| variables.c.contains(&original_item));

        let integer_source_key = self
            .typed_variables
            .as_ref()
            .is_some_and(|replacements| replacements.integer.contains_key(&original_accumulator));
        let integer_item_source_key = self
            .typed_variables
            .as_ref()
            .is_some_and(|replacements| replacements.integer.contains_key(&original_item));
        let c_item_source_key = self
            .typed_variables
            .as_ref()
            .is_some_and(|replacements| replacements.c.contains_key(&original_item));
        let accumulator_blocks_source = self.integer_shadowed
            || integer_source == Some(original_accumulator)
            || integer_source_key;
        let item_blocks_source = if item_is_integer {
            self.integer_shadowed
                || integer_source == Some(original_item)
                || integer_item_source_key
        } else {
            c_source == Some(original_item) || c_item_source_key
        };
        let typed_mode = self.typed_variables.is_some();
        let accumulator_capture = if typed_mode {
            typed_integer_replacement_contains
        } else {
            integer_replacement_contains && !accumulator_blocks_source
        };
        let item_capture = if item_is_integer {
            if typed_mode {
                typed_integer_item_replacement_contains
            } else {
                self.integer_replacement_variables
                    .as_ref()
                    .is_some_and(|variables| variables.contains(&original_item))
                    && !item_blocks_source
            }
        } else if typed_mode {
            typed_c_replacement_contains
        } else {
            c_replacement_contains && !item_blocks_source
        };

        // Fold endpoints and the initial value live outside the body scope.
        let index = match index {
            IntegerRangeFoldIndex::Int32 { start, end } => {
                let start = self.bits(start.value());
                if self.checked_work_exhausted() {
                    return IntegerTerm::constant_i64(0);
                }
                let end = self.bits(end.value());
                IntegerRangeFoldIndex::Int32 {
                    start: SharedIntegerRangeEndpoint::intern(start),
                    end: SharedIntegerRangeEndpoint::intern(end),
                }
            }
            IntegerRangeFoldIndex::Integer { start, end } => {
                let start = self.integer_shared(start).into();
                if self.checked_work_exhausted() {
                    return IntegerTerm::constant_i64(0);
                }
                let end = self.integer_shared(end).into();
                IntegerRangeFoldIndex::Integer { start, end }
            }
        };
        let initial = self.integer_shared(initial).into();
        if self.checked_work_exhausted() {
            return IntegerTerm::constant_i64(0);
        }

        let body_variable_max = if accumulator_capture || item_capture {
            self.body_variable_max(body)
        } else {
            0
        };
        if self.checked_work_exhausted() {
            return IntegerTerm::constant_i64(0);
        }
        let mut fresh_upper = body_variable_max
            .max(self.integer_replacement_variable_max.unwrap_or(0))
            .max(self.bitvector_replacement_variable_max.unwrap_or(0))
            .max(self.integer_renaming_max.unwrap_or(0))
            .max(self.scope_renaming_max)
            .max(original_accumulator.0)
            .max(original_item.0);
        if let Some(source) = integer_source {
            fresh_upper = fresh_upper.max(source.0);
        }
        if let Some(source) = c_source {
            fresh_upper = fresh_upper.max(source.0);
        }
        let mut accumulator = original_accumulator;
        let mut item = original_item;
        if (accumulator_capture || item_capture)
            && let Some(next) = fresh_upper.checked_add(1)
        {
            self.fresh_next = self.fresh_next.max(next);
        } else if accumulator_capture || item_capture {
            self.integer_work_exhausted = true;
            return IntegerTerm::constant_i64(0);
        }
        if accumulator_capture {
            let Some(fresh) = self.fresh_variable() else {
                return IntegerTerm::constant_i64(0);
            };
            accumulator = fresh;
            self.scope_renaming_max = self.scope_renaming_max.max(accumulator.0);
        }
        if item_capture {
            let Some(fresh) = self.fresh_variable() else {
                return IntegerTerm::constant_i64(0);
            };
            item = fresh;
            self.scope_renaming_max = self.scope_renaming_max.max(item.0);
        }

        let accumulator_scope_shadowed = self.scope.integer.contains_key(&original_accumulator);
        let item_scope_shadowed = if item_is_integer {
            self.scope.integer.contains_key(&original_item)
        } else {
            self.scope.c.contains_key(&original_item)
        };
        let changed_scope = accumulator_capture
            || item_capture
            || accumulator_blocks_source
            || item_blocks_source
            || accumulator_scope_shadowed
            || item_scope_shadowed;
        let mapping_shadows_integer_source =
            self.integer_variables.as_ref().is_some_and(|mapping| {
                mapping.from == original_accumulator
                    || (item_is_integer && mapping.from == original_item)
            });

        let body = if !changed_scope {
            self.integer_shared(body).into()
        } else {
            let parent_scope = self.scope_id;
            let parent_shadowed = self.integer_shadowed;
            self.bump_scope_id();
            if self.checked_work_exhausted() {
                return IntegerTerm::constant_i64(0);
            }
            let mut changes = Vec::new();
            self.remove_fold_scope_mapping(true, original_accumulator, &mut changes);
            if item_is_integer {
                self.remove_fold_scope_mapping(true, original_item, &mut changes);
            } else {
                self.remove_fold_scope_mapping(false, original_item, &mut changes);
            }
            if accumulator_capture {
                self.push_fold_scope_mapping(true, original_accumulator, accumulator, &mut changes);
            } else {
                // Every fold binder hides an outer substitution at the same
                // carrier and ID, even when no freshening was needed.
                self.push_fold_scope_mapping(
                    true,
                    original_accumulator,
                    original_accumulator,
                    &mut changes,
                );
            }
            if item_capture {
                self.push_fold_scope_mapping(item_is_integer, original_item, item, &mut changes);
            } else {
                self.push_fold_scope_mapping(
                    item_is_integer,
                    original_item,
                    original_item,
                    &mut changes,
                );
            }
            if mapping_shadows_integer_source {
                self.integer_shadowed = true;
            }
            let body = self.integer_shared(body).into();
            self.restore_fold_scope_mappings(&changes);
            self.integer_shadowed = parent_shadowed;
            self.scope_id = parent_scope;
            body
        };

        IntegerTerm::RangeFold {
            index,
            initial,
            accumulator,
            item,
            body,
        }
    }

    fn scope_key(&self) -> u64 {
        self.scope_id
    }

    fn rewrite_integer_variable(&mut self, variable: Variable) -> IntegerTerm {
        if let Some(mapped) = self.scope.integer.get(&variable) {
            return IntegerTerm::Variable(*mapped);
        }
        if !self.source_disabled
            && !self.integer_shadowed
            && let Some(replacements) = &self.typed_variables
            && let Some(replacement) = replacements.integer.get(&variable)
        {
            self.charge_rewrite_work(1);
            if self.integer_work_exhausted {
                return IntegerTerm::Variable(variable);
            }
            self.changed = true;
            // Replacement terms are from the enclosing scope.  Never walk
            // them under a nested match's lexical mappings.
            return replacement.clone();
        }
        let Some(mapping) = &self.integer_variables else {
            return IntegerTerm::Variable(variable);
        };
        if let Some(mapped) = mapping.renamings.get(&variable) {
            return IntegerTerm::Variable(*mapped);
        }
        if self.source_disabled || self.integer_shadowed || variable != mapping.from {
            return IntegerTerm::Variable(variable);
        }
        let replacement = mapping.to.clone();
        let work = match &replacement {
            IntegerTerm::Constant(value) => value.bits() as usize + 1,
            _ => 1,
        };
        self.integer_work_exhausted |= crate::instrumentation::deadline_exceeded_with_work(work);
        if self.integer_work_exhausted {
            return IntegerTerm::Variable(variable);
        }
        // Do not walk the replacement under the current lexical scope.  The
        // replacement's variables are free in this occurrence and must not
        // be remapped by an arm binder (or recursively substitute `from`).
        replacement
    }

    fn rewrite_integer_match(
        &mut self,
        original_scrutinee: &AlgebraicTerm,
        arms: &[crate::kernel::AlgebraicIntegerMatchArm],
    ) -> IntegerTerm {
        let exhausted = || IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(exhausted_algebraic(original_scrutinee)),
            arms: Vec::new(),
        };
        self.reserve_match_variables(original_scrutinee, arms);
        if self.integer_work_exhausted {
            return exhausted();
        }
        let scrutinee = self.algebraic(original_scrutinee);
        if self.integer_work_exhausted {
            return exhausted();
        }
        let mut rewritten_arms = Vec::with_capacity(arms.len());
        for arm in arms {
            // Pattern declarations are already in the carrier of the arm.
            // Rewrite only their identity after installing the arm scope; a
            // normal term walk here would substitute a declaration itself.
            let saved_scope_id = self.scope_id;
            let saved_shadowed = self.integer_shadowed;
            let mut changes = Vec::new();
            let mut bindings = arm.bindings.clone();
            if !self.rewrite_match_bindings(&mut bindings, &mut changes) {
                self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                return exhausted();
            }
            let body = self.integer(&arm.body).into();
            self.restore_scope(&changes, saved_scope_id, saved_shadowed);
            if self.integer_work_exhausted {
                return exhausted();
            }
            rewritten_arms.push(crate::kernel::AlgebraicIntegerMatchArm {
                variant: arm.variant.clone(),
                bindings,
                body,
            });
        }
        if let Some(value) = self.rewrite_integer_match_iota(&scrutinee, &rewritten_arms) {
            return value;
        }
        if self.integer_work_exhausted {
            return exhausted();
        }
        IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(scrutinee),
            arms: rewritten_arms,
        }
    }

    fn rewrite_integer_match_iota(
        &mut self,
        scrutinee: &AlgebraicTerm,
        arms: &[crate::kernel::AlgebraicIntegerMatchArm],
    ) -> Option<IntegerTerm> {
        let fields = scrutinee.checked_constructor_fields()?;
        let variant = match &scrutinee.node {
            AlgebraicTermNode::Constructor { variant, .. } => variant,
            _ => unreachable!(),
        };
        let arm = arms.iter().find(|arm| arm.variant == *variant)?;
        let schema = scrutinee
            .algebraic_type
            .variants
            .iter()
            .find(|schema| schema.name == *variant)?;
        if arm.bindings.len() != fields.len() {
            return None;
        }
        let mut c_replacements = BTreeMap::new();
        let mut integer_replacements = BTreeMap::new();
        let mut algebraic_replacements = BTreeMap::new();
        for ((binding, field), expected) in arm.bindings.iter().zip(fields).zip(&schema.fields) {
            if field.value_type() != *expected {
                return None;
            }
            let (carrier, variable) = typed_binding_variable(expected, binding)?;
            let duplicate = match (carrier, field) {
                (BindingCarrier::C, AlgebraicValue::C(value)) => {
                    let replacement = typed_c_replacement(value)?;
                    c_replacements.insert(variable, replacement).is_some()
                }
                (BindingCarrier::Integer, AlgebraicValue::Integer(value)) => integer_replacements
                    .insert(variable, value.clone())
                    .is_some(),
                (BindingCarrier::Algebraic, AlgebraicValue::Algebraic(value)) => {
                    algebraic_replacements
                        .insert(variable, value.clone())
                        .is_some()
                }
                _ => return None,
            };
            if duplicate {
                return None;
            }
        }
        let mut field_rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let value = field_rewrite.integer(&arm.body);
        self.changed |= field_rewrite.changed;
        self.unsupported_integer_scope |= field_rewrite.unsupported_integer_scope;
        self.integer_work_exhausted |= field_rewrite.integer_work_exhausted;
        #[cfg(test)]
        {
            self.visits += field_rewrite.visits;
        }
        if self.unsupported_integer_scope || self.integer_work_exhausted {
            return None;
        }
        self.changed = true;
        Some(value)
    }

    fn rewrite_match_bindings(
        &mut self,
        bindings: &mut [AlgebraicValue],
        changes: &mut Vec<ScopeChange>,
    ) -> bool {
        self.ensure_replacement_carriers();
        for binding in bindings {
            let Some((carrier, variable)) = binding_variable(binding) else {
                continue;
            };
            if matches!(carrier, BindingCarrier::C) && self.has_composite_bitvector_source() {
                self.unsupported_integer_scope = true;
                return false;
            }
            let replacement_capture = self
                .replacement_carriers
                .as_ref()
                .is_some_and(|replacement| replacement.contains(carrier, variable));
            if replacement_capture {
                let Some(fresh) = self.fresh_variable() else {
                    return false;
                };
                self.push_binding_mapping(carrier, variable, fresh, changes);
                replace_binding_variable(binding, carrier, fresh);
            } else if self.binding_shadows_source(carrier, variable) {
                self.push_binding_mapping(carrier, variable, variable, changes);
                if matches!(carrier, BindingCarrier::Integer) && !self.integer_shadowed {
                    self.integer_shadowed = true;
                    self.bump_scope_id();
                }
            }
            if self.integer_work_exhausted {
                return false;
            }
        }
        true
    }

    fn rewrite_c_binder(
        &mut self,
        variable: Variable,
        changes: &mut Vec<ScopeChange>,
    ) -> Option<Variable> {
        if self.has_composite_bitvector_source() {
            self.unsupported_integer_scope = true;
            return None;
        }
        self.ensure_replacement_carriers();
        if self
            .replacement_carriers
            .as_ref()
            .is_some_and(|replacement| replacement.contains(BindingCarrier::C, variable))
        {
            let fresh = self.fresh_variable()?;
            self.push_binding_mapping(BindingCarrier::C, variable, fresh, changes);
            return Some(fresh);
        }
        if self.binding_shadows_source(BindingCarrier::C, variable) {
            self.push_binding_mapping(BindingCarrier::C, variable, variable, changes);
            return Some(variable);
        }
        Some(variable)
    }

    fn has_composite_bitvector_source(&self) -> bool {
        self.bitvector
            .is_some_and(|(source, _)| !matches!(source, Bitvector32Term::Variable(_)))
    }

    fn reserve_algebraic_match_variables(
        &mut self,
        _term: &AlgebraicTerm,
        scrutinee: &AlgebraicTerm,
        arms: &[AlgebraicResultMatchArm],
    ) {
        self.ensure_replacement_carriers();
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        collect_algebraic_carriers_seen(scrutinee, &mut variables, &mut seen);
        if variables.exhausted() {
            self.reserve_source_variables(variables);
            return;
        }
        for arm in arms {
            for binding in &arm.bindings {
                collect_algebraic_value_carriers(binding, &mut variables, &mut seen);
                if variables.exhausted() {
                    self.reserve_source_variables(variables);
                    return;
                }
            }
            collect_algebraic_carriers_seen(&arm.body, &mut variables, &mut seen);
            if variables.exhausted() {
                self.reserve_source_variables(variables);
                return;
            }
        }
        self.reserve_source_variables(variables);
    }

    fn reserve_bitvector_scope_variables(&mut self, term: &Bitvector32Term) {
        self.ensure_replacement_carriers();
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        collect_bitvector_carriers(term, &mut variables);
        self.reserve_source_variables(variables);
    }

    fn binding_shadows_source(&self, carrier: BindingCarrier, variable: Variable) -> bool {
        match carrier {
            BindingCarrier::C => {
                matches!(
                    self.bitvector,
                    Some((Bitvector32Term::Variable(source), _)) if *source == variable
                ) || self
                    .pointer_variable
                    .is_some_and(|(source, _)| source == variable)
                    || self
                        .typed_variables
                        .as_ref()
                        .is_some_and(|replacements| replacements.c.contains_key(&variable))
            }
            BindingCarrier::Integer => {
                self.integer_variables
                    .as_ref()
                    .is_some_and(|mapping| mapping.from == variable)
                    || self
                        .typed_variables
                        .as_ref()
                        .is_some_and(|replacements| replacements.integer.contains_key(&variable))
            }
            BindingCarrier::Algebraic => {
                matches!(
                    self.algebraic,
                    Some((AlgebraicTerm { node: AlgebraicTermNode::Variable(source), .. }, _))
                        if *source == variable
                ) || self
                    .typed_variables
                    .as_ref()
                    .is_some_and(|replacements| replacements.algebraic.contains_key(&variable))
            }
        }
    }

    fn push_binding_mapping(
        &mut self,
        carrier: BindingCarrier,
        from: Variable,
        to: Variable,
        changes: &mut Vec<ScopeChange>,
    ) {
        let previous = match carrier {
            BindingCarrier::C => self.scope.c.insert(from, to),
            BindingCarrier::Integer => self.scope.integer.insert(from, to),
            BindingCarrier::Algebraic => self.scope.algebraic.insert(from, to),
        };
        match carrier {
            BindingCarrier::C => changes.push(ScopeChange::C(from, previous)),
            BindingCarrier::Integer => changes.push(ScopeChange::Integer(from, previous)),
            BindingCarrier::Algebraic => changes.push(ScopeChange::Algebraic(from, previous)),
        }
        if previous != Some(to) {
            self.bump_scope_id();
        }
    }

    fn restore_scope(&mut self, changes: &[ScopeChange], scope_id: u64, integer_shadowed: bool) {
        self.charge_rewrite_work(changes.len());
        for change in changes.iter().rev() {
            match change {
                ScopeChange::C(variable, previous) => {
                    restore_mapping(&mut self.scope.c, *variable, *previous)
                }
                ScopeChange::Integer(variable, previous) => {
                    restore_mapping(&mut self.scope.integer, *variable, *previous)
                }
                ScopeChange::Algebraic(variable, previous) => {
                    restore_mapping(&mut self.scope.algebraic, *variable, *previous)
                }
            }
        }
        self.scope_id = scope_id;
        self.integer_shadowed = integer_shadowed;
    }

    fn reserve_match_variables(
        &mut self,
        scrutinee: &AlgebraicTerm,
        arms: &[crate::kernel::AlgebraicIntegerMatchArm],
    ) {
        self.ensure_replacement_carriers();
        if self.source_variables_reserved {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        collect_algebraic_carriers_seen(scrutinee, &mut variables, &mut seen);
        if variables.exhausted() {
            self.reserve_source_variables(variables);
            return;
        }
        for arm in arms {
            for binding in &arm.bindings {
                collect_algebraic_value_carriers(binding, &mut variables, &mut seen);
                if variables.exhausted() {
                    self.reserve_source_variables(variables);
                    return;
                }
            }
            collect_integer_shared_carriers(&arm.body, &mut variables, &mut seen);
            if variables.exhausted() {
                self.reserve_source_variables(variables);
                return;
            }
        }
        self.reserve_source_variables(variables);
    }

    fn ensure_replacement_carriers(&mut self) {
        if self.replacement_carriers.is_some() {
            return;
        }
        let mut variables = self.new_carrier_variables();
        let mut seen = BTreeSet::new();
        if let Some(mapping) = &self.integer_variables {
            collect_integer_carriers(mapping.to, &mut variables, &mut seen);
        }
        if !variables.exhausted()
            && let Some((_, to)) = self.bitvector
        {
            collect_bitvector_carriers(to, &mut variables);
        }
        if !variables.exhausted()
            && let Some((_, to)) = self.algebraic
        {
            collect_algebraic_carriers_seen(to, &mut variables, &mut seen);
        }
        if !variables.exhausted()
            && let Some((_, to)) = self.pointer_variable
        {
            collect_pointer_carriers(to, &mut variables);
        }
        if !variables.exhausted()
            && let Some(replacements) = &self.typed_variables
        {
            for replacement in replacements.c.values() {
                match replacement {
                    TypedCReplacement::Bitvector(value) => {
                        collect_bitvector_carriers(value, &mut variables)
                    }
                    TypedCReplacement::Pointer(pointer) => {
                        collect_pointer_carriers(pointer, &mut variables);
                    }
                }
                if variables.exhausted() {
                    break;
                }
            }
            for replacement in replacements.integer.values() {
                if variables.exhausted() {
                    break;
                }
                collect_integer_carriers(replacement, &mut variables, &mut seen);
            }
            for replacement in replacements.algebraic.values() {
                if variables.exhausted() {
                    break;
                }
                collect_algebraic_carriers_seen(replacement, &mut variables, &mut seen);
            }
        }
        #[cfg(test)]
        {
            self.collector_visits = self.collector_visits.saturating_add(variables.nodes);
        }
        self.integer_work_exhausted |= variables.work_exhausted;
        if self.integer_work_exhausted {
            self.replacement_carriers = Some(variables);
            return;
        }
        self.charge_rewrite_work(1);
        if self.integer_work_exhausted {
            self.replacement_carriers = Some(variables);
            return;
        }
        self.extend_reserved_variables(&variables);
        self.replacement_carriers = Some(variables);
    }

    fn bump_scope_id(&mut self) {
        self.charge_rewrite_work(1);
        if let Some(next) = self.next_scope_id.checked_add(1) {
            self.scope_id = self.next_scope_id;
            self.next_scope_id = next;
        } else {
            self.integer_work_exhausted = true;
        }
    }

    fn fresh_variable(&mut self) -> Option<Variable> {
        if self.integer_work_exhausted {
            return None;
        }
        loop {
            let variable = Variable(self.fresh_next);
            let Some(next) = self.fresh_next.checked_add(1) else {
                self.integer_work_exhausted = true;
                return None;
            };
            self.fresh_next = next;
            self.charge_rewrite_work(1);
            if self.reserved_variables.insert(variable) {
                return Some(variable);
            }
        }
    }

    fn charge_rewrite_work(&mut self, work: usize) {
        if self.integer_variables.is_some()
            || self.typed_variables.is_some()
            || self.enforce_integer_work_limit
        {
            self.integer_work_exhausted |=
                crate::instrumentation::deadline_exceeded_with_work(work);
        } else {
            crate::instrumentation::record_deterministic_work(work);
        }
    }

    fn pointer(&mut self, p: &Pointer) -> Pointer {
        if self.checked_work_exhausted() {
            return exhausted_pointer();
        }
        if let PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) =
            &p.block
            && let Some(mapped) = self.scope.c.get(variable)
        {
            let mapped = *mapped;
            let offset = self.offset(&p.offset);
            if self.checked_work_exhausted() {
                return exhausted_pointer();
            }
            return Pointer {
                block: match &p.block {
                    PointerBlock::FunctionSymbolic(_) => PointerBlock::FunctionSymbolic(mapped),
                    _ => PointerBlock::Symbolic(mapped),
                },
                offset,
            };
        }
        if let PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) =
            &p.block
            && let Some(replacements) = &self.typed_variables
            && let Some(TypedCReplacement::Pointer(replacement)) = replacements.c.get(variable)
        {
            self.changed = true;
            let offset = self.offset(&p.offset);
            if self.checked_work_exhausted() {
                return exhausted_pointer();
            }
            return Pointer {
                block: replacement.block.clone(),
                offset: PointerOffsetTerm::add(replacement.offset.clone(), offset),
            };
        }
        if let Some((from, to)) = self.pointer_variable
            && matches!(&p.block, PointerBlock::Symbolic(variable) | PointerBlock::FunctionSymbolic(variable) if *variable == from)
        {
            self.changed = true;
            let offset = self.offset(&p.offset);
            if self.checked_work_exhausted() {
                return exhausted_pointer();
            }
            return Pointer {
                block: to.block.clone(),
                offset: PointerOffsetTerm::add(to.offset.clone(), offset),
            };
        }
        let offset = self.offset(&p.offset);
        if self.checked_work_exhausted() {
            return exhausted_pointer();
        }
        Pointer {
            block: p.block.clone(),
            offset,
        }
    }
    fn offset(&mut self, v: &PointerOffsetTerm) -> PointerOffsetTerm {
        if self.checked_work_exhausted() {
            return exhausted_offset();
        }
        let result = match v {
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
        };
        if self.checked_work_exhausted() {
            exhausted_offset()
        } else {
            result
        }
    }
    pub(crate) fn condition(&mut self, v: &ConditionTerm) -> ConditionTerm {
        self.reserve_condition_variables_once(v);
        if self.checked_work_exhausted() {
            return ConditionTerm::Constant(false);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return ConditionTerm::Constant(false);
        }
        if let Some(conditions) = self.conditions
            && let Some(value) = conditions.get(v)
        {
            return ConditionTerm::Constant(*value);
        }
        let result = match v {
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
                if self.integer_variables.is_some() {
                    ConditionTerm::IntegerLessThan(self.integer(a).into(), self.integer(b).into())
                } else {
                    ConditionTerm::integer_less_than(self.integer(a), self.integer(b))
                }
            }
            ConditionTerm::IntegerLessEqual(a, b) => {
                if self.integer_variables.is_some() {
                    ConditionTerm::IntegerLessEqual(self.integer(a).into(), self.integer(b).into())
                } else {
                    ConditionTerm::integer_less_equal(self.integer(a), self.integer(b))
                }
            }
            ConditionTerm::IntegerGreaterThan(a, b) => {
                if self.integer_variables.is_some() {
                    ConditionTerm::IntegerGreaterThan(
                        self.integer(a).into(),
                        self.integer(b).into(),
                    )
                } else {
                    ConditionTerm::integer_greater_than(self.integer(a), self.integer(b))
                }
            }
            ConditionTerm::IntegerGreaterEqual(a, b) => {
                if self.integer_variables.is_some() {
                    ConditionTerm::IntegerGreaterEqual(
                        self.integer(a).into(),
                        self.integer(b).into(),
                    )
                } else {
                    ConditionTerm::integer_greater_equal(self.integer(a), self.integer(b))
                }
            }
            ConditionTerm::IntegerEqual(a, b) => {
                if self.integer_variables.is_some() {
                    ConditionTerm::IntegerEqual(self.integer(a).into(), self.integer(b).into())
                } else {
                    ConditionTerm::integer_equal(self.integer(a), self.integer(b))
                }
            }
            ConditionTerm::IntegerNotEqual(a, b) => {
                if self.integer_variables.is_some() {
                    ConditionTerm::IntegerNotEqual(self.integer(a).into(), self.integer(b).into())
                } else {
                    ConditionTerm::integer_not_equal(self.integer(a), self.integer(b))
                }
            }
        };
        if self.checked_work_exhausted() {
            ConditionTerm::Constant(false)
        } else {
            result
        }
    }
    pub(crate) fn bits(&mut self, v: &Bitvector32Term) -> Bitvector32Term {
        self.reserve_bitvector_variables_once(v);
        if self.checked_work_exhausted() {
            return Bitvector32Term::Constant(0);
        }
        self.visit();
        if self.checked_work_exhausted() {
            return Bitvector32Term::Constant(0);
        }
        if let Bitvector32Term::Variable(variable) = v
            && let Some(mapped) = self.scope.c.get(variable)
        {
            return Bitvector32Term::Variable(*mapped);
        }
        if let Bitvector32Term::Variable(variable) = v
            && let Some(replacements) = &self.typed_variables
            && let Some(TypedCReplacement::Bitvector(replacement)) = replacements.c.get(variable)
        {
            self.changed = true;
            return replacement.clone();
        }
        if let Some((from, to)) = self.bitvector
            && !self.source_disabled
            && v == from
        {
            self.changed = true;
            return to.clone();
        }
        let result = match v {
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
            } => {
                self.reserve_bitvector_scope_variables(v);
                if self.checked_work_exhausted() {
                    return Bitvector32Term::Constant(0);
                }
                let start = self.bits(start);
                if self.checked_work_exhausted() {
                    return Bitvector32Term::Constant(0);
                }
                let end = self.bits(end);
                if self.checked_work_exhausted() {
                    return Bitvector32Term::Constant(0);
                }
                let initial = self.bits(initial);
                if self.checked_work_exhausted() {
                    return Bitvector32Term::Constant(0);
                }
                let saved_scope_id = self.scope_id;
                let saved_shadowed = self.integer_shadowed;
                let mut changes = Vec::new();
                let Some(accumulator) = self.rewrite_c_binder(*accumulator, &mut changes) else {
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    return Bitvector32Term::Constant(0);
                };
                let Some(item) = self.rewrite_c_binder(*item, &mut changes) else {
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    return Bitvector32Term::Constant(0);
                };
                let body = if self.conditions.is_some() {
                    body.clone()
                } else {
                    Box::new(self.bits(body))
                };
                self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                if self.checked_work_exhausted() {
                    return Bitvector32Term::Constant(0);
                }
                Bitvector32Term::RangeFold {
                    start: Box::new(start),
                    end: Box::new(end),
                    initial: Box::new(initial),
                    accumulator,
                    item,
                    body,
                }
            }
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                let mut rewritten = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    rewritten.push(self.bits(argument));
                    if self.checked_work_exhausted() {
                        return Bitvector32Term::Constant(0);
                    }
                }
                Bitvector32Term::PureFunctionApplication {
                    name: name.clone(),
                    arguments: rewritten,
                }
            }
            Bitvector32Term::ClickFunctionApplication { name, arguments } => {
                let mut rewritten = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    rewritten.push(self.argument(argument));
                    if self.checked_work_exhausted() {
                        return Bitvector32Term::Constant(0);
                    }
                }
                Bitvector32Term::ClickFunctionApplication {
                    name: name.clone(),
                    arguments: rewritten,
                }
            }
            Bitvector32Term::AlgebraicMatch { scrutinee, arms } => {
                self.reserve_bitvector_scope_variables(v);
                if self.checked_work_exhausted() {
                    return Bitvector32Term::Constant(0);
                }
                let scrutinee = self.algebraic(scrutinee);
                if self.checked_work_exhausted() {
                    return Bitvector32Term::Constant(0);
                }
                let mut rewritten_arms = Vec::with_capacity(arms.len());
                for arm in arms {
                    let saved_scope_id = self.scope_id;
                    let saved_shadowed = self.integer_shadowed;
                    let mut changes = Vec::new();
                    let mut bindings = arm.bindings.clone();
                    if !self.rewrite_match_bindings(&mut bindings, &mut changes) {
                        self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                        return Bitvector32Term::Constant(0);
                    }
                    let body = if self.conditions.is_some() {
                        arm.body.clone()
                    } else {
                        self.bits(&arm.body)
                    };
                    self.restore_scope(&changes, saved_scope_id, saved_shadowed);
                    if self.checked_work_exhausted() {
                        return Bitvector32Term::Constant(0);
                    }
                    rewritten_arms.push(AlgebraicBitvectorMatchArm {
                        variant: arm.variant.clone(),
                        bindings,
                        body,
                    });
                }
                Bitvector32Term::AlgebraicMatch {
                    scrutinee: Box::new(scrutinee),
                    arms: rewritten_arms,
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
        };
        if self.checked_work_exhausted() {
            Bitvector32Term::Constant(0)
        } else {
            result
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
    fn nested_c_folds_and_adt_matches_reserve_actual_nodes_linearly() {
        let mut work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
                name: "Case".into(),
                fields: vec![AlgebraicValueType::C(CType::Int32)],
            }]
            .into();
            let value_type = AlgebraicValueType::Algebraic {
                name: "FoldMatch".into(),
                arguments: vec![],
            };
            let algebraic_type = AlgebraicType {
                rigid: false,
                name: "FoldMatch".into(),
                arguments: vec![],
                variants: variants.clone(),
                schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                    value_type, variants,
                )]))),
            };
            let mut expression = IntegerTerm::constant_i64(0);
            for index in 0..depth {
                let binding = Variable(10_000 + index as u64);
                let accumulator = Variable(11_000 + index as u64);
                let item = Variable(12_000 + index as u64);
                let fold = Bitvector32Term::RangeFold {
                    start: Box::new(Bitvector32Term::Constant(0)),
                    end: Box::new(Bitvector32Term::Constant(2)),
                    initial: Box::new(Bitvector32Term::Constant(0)),
                    accumulator,
                    item,
                    body: Box::new(Bitvector32Term::Variable(accumulator)),
                };
                let observed =
                    IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                        "observe_fold".into(),
                        vec![PureFunctionArgument::Value(CValue::Int32(fold))],
                    ));
                let body = IntegerTerm::Add(observed.into(), expression.into());
                expression = IntegerTerm::AlgebraicMatch {
                    scrutinee: Box::new(AlgebraicTerm {
                        algebraic_type: algebraic_type.clone(),
                        node: AlgebraicTermNode::Variable(Variable(13_000 + index as u64)),
                    }),
                    arms: vec![AlgebraicIntegerMatchArm {
                        variant: "Case".into(),
                        bindings: vec![AlgebraicValue::C(CValue::Int32(
                            Bitvector32Term::Variable(binding),
                        ))],
                        body: body.into(),
                    }],
                };
            }
            let (visits, measured) = crate::instrumentation::measure_deterministic_work(|| {
                let conditions = HashMap::new();
                let mut rewrite = TermRewrite::for_conditions(&conditions);
                let _ = rewrite.term(&Term::Integer(expression.clone()));
                rewrite.visits
            });
            assert!(visits >= depth, "nested match traversal was skipped");
            work.push(measured);
        }
        for pair in work.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "nested carrier reservation expanded superlinearly: {work:?}"
            );
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

    #[test]
    fn array_ref_rewrite_preserves_opaque_memory_and_ignores_unrelated_blocks() {
        let source = Variable(9880);
        let replacement = Pointer {
            block: PointerBlock::Symbolic(Variable(9881)),
            offset: PointerOffsetTerm::Constant(3),
        };
        let expected_pointer = Pointer {
            block: replacement.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        };
        let input_pointer = Pointer {
            block: PointerBlock::Symbolic(source),
            offset: PointerOffsetTerm::Constant(1),
        };
        let memory_with_unrelated_blocks = |count: u64| {
            let mut memory = CMemory::new().with_block("array", 8);
            for index in 0..count {
                memory = memory.with_block(PointerBlock::Heap(index + 1), 8);
            }
            memory
        };
        let observed_array = |memory: CMemory, pointer: Pointer| {
            Term::Integer(IntegerTerm::PureFunctionApplication(
                SharedIntegerApplication::intern(
                    "observe_array".into(),
                    vec![PureFunctionArgument::ArrayRef {
                        memory,
                        pointer: CValue::Pointer(CPointerValue::new(pointer, CType::VoidPointer)),
                        element_type: CType::UInt8,
                    }],
                ),
            ))
        };
        let rewrite = |term: &Term| {
            let mut walker = TermRewrite::for_pointer_variable(source, &replacement);
            walker.term(term)
        };
        let small_memory = memory_with_unrelated_blocks(0);
        let large_memory = memory_with_unrelated_blocks(256);
        let small_input = observed_array(small_memory.clone(), input_pointer.clone());
        let large_input = observed_array(large_memory.clone(), input_pointer);
        let (small, small_work) =
            crate::instrumentation::measure_deterministic_work(|| rewrite(&small_input));
        let (large, large_work) =
            crate::instrumentation::measure_deterministic_work(|| rewrite(&large_input));

        let assert_rewrite = |output: &Term, original_memory: &CMemory| {
            let Term::Integer(IntegerTerm::PureFunctionApplication(application)) = output else {
                unreachable!()
            };
            let [
                PureFunctionArgument::ArrayRef {
                    memory,
                    pointer: CValue::Pointer(pointer),
                    element_type,
                },
            ] = application.arguments()
            else {
                unreachable!()
            };
            assert_eq!(pointer.pointer(), &expected_pointer);
            assert_eq!(*element_type, CType::UInt8);
            assert!(std::sync::Arc::ptr_eq(
                &memory.blocks,
                &original_memory.blocks
            ));
            assert!(std::sync::Arc::ptr_eq(
                &memory.cells,
                &original_memory.cells
            ));
            assert!(std::sync::Arc::ptr_eq(
                &memory.union_cells,
                &original_memory.union_cells
            ));
            assert!(std::sync::Arc::ptr_eq(
                &memory.ended_local_blocks,
                &original_memory.ended_local_blocks
            ));
            assert!(std::sync::Arc::ptr_eq(&memory.heap, &original_memory.heap));
        };
        assert_rewrite(&small, &small_memory);
        assert_rewrite(&large, &large_memory);
        assert_eq!(small_work, large_work);

        let mut c_replacements = BTreeMap::new();
        c_replacements.insert(source, TypedCReplacement::Pointer(replacement.clone()));
        let empty_integer_replacements = BTreeMap::new();
        let empty_algebraic_replacements = BTreeMap::new();
        let mut typed_rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &empty_integer_replacements,
            &empty_algebraic_replacements,
        );
        let typed_output = typed_rewrite.term(&small_input);
        assert_rewrite(&typed_output, &small_memory);
    }

    #[test]
    fn typed_condition_budget_stops_deep_c_and_ignores_snapshot_size() {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 16,
            smart: 16,
            control: 16,
        };
        let tactic = crate::instrumentation::TacticEvent {
            claim: "integer.typed_condition_budget".into(),
            tactic_index: 0,
            tactic_name: "typed_condition_budget".into(),
            class: "simple".into(),
            statement_index: 0,
            source_index: 0,
        };
        let source = Variable(9890);
        let replacement = Variable(9891);
        let pointer = Pointer {
            block: PointerBlock::Symbolic(source),
            offset: PointerOffsetTerm::Constant(0),
        };
        let condition_for = |memory: CMemory, depth: usize, fanout: usize| {
            let mut right = Bitvector32Term::Variable(source);
            for index in 0..depth as u64 {
                let mut arguments = Vec::with_capacity(fanout + 1);
                arguments.push(PureFunctionArgument::Value(CValue::Int32(right)));
                arguments.extend((0..fanout).map(|_| {
                    PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Constant(0)))
                }));
                let fanout = Bitvector32Term::ClickFunctionApplication {
                    name: "wide_condition".into(),
                    arguments,
                };
                right = Bitvector32Term::If {
                    condition: Box::new(ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(20_000 + index))),
                        Box::new(Bitvector32Term::Constant(0)),
                    )),
                    then_term: Box::new(fanout),
                    else_term: Box::new(Bitvector32Term::Constant(0)),
                };
            }
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::MemoryLoad(
                    memory.into(),
                    Box::new(pointer.clone()),
                )),
                Box::new(right),
            )
        };
        let memory_with_unrelated_blocks = |count: u64| {
            let mut memory = CMemory::new().with_block("array", 8);
            for index in 0..count {
                memory = memory.with_block(PointerBlock::Heap(index + 1), 8);
            }
            memory
        };
        let run = |condition: ConditionTerm, tactic: crate::instrumentation::TacticEvent| {
            let c_replacements = BTreeMap::from([(
                source,
                TypedCReplacement::Bitvector(Bitvector32Term::Variable(replacement)),
            )]);
            let integer_replacements = BTreeMap::new();
            let algebraic_replacements = BTreeMap::new();
            crate::instrumentation::with_tactic_work_limits(limits, || {
                crate::instrumentation::collect(|| {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                    );
                    let mut rewrite = TermRewrite::for_typed_variables(
                        &c_replacements,
                        &integer_replacements,
                        &algebraic_replacements,
                    );
                    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                        rewrite.term(&Term::Condition(condition))
                    });
                    let result = (
                        rewrite.integer_work_exhausted,
                        rewrite.visits,
                        rewrite.collector_visits,
                        work,
                    );
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                    );
                    result
                })
                .0
            })
        };
        for (index, &(depth, fanout)) in [(8usize, 8usize), (16, 16), (32, 32), (64, 64)]
            .iter()
            .enumerate()
        {
            let mut small_tactic = tactic.clone();
            small_tactic.tactic_index = index * 2;
            let mut large_tactic = tactic.clone();
            large_tactic.tactic_index = index * 2 + 1;
            let small = run(
                condition_for(memory_with_unrelated_blocks(0), depth, fanout),
                small_tactic,
            );
            let large = run(
                condition_for(memory_with_unrelated_blocks(256), depth, fanout),
                large_tactic,
            );
            assert!(
                small.0 && large.0,
                "deep carrier collection must be bounded at depth {depth}"
            );
            assert!(small.1 <= 16 && large.1 <= 16);
            assert!(small.2 <= 32 && large.2 <= 32);
            assert!(small.3 <= 32 && large.3 <= 32);
            assert_eq!(
                small.2, large.2,
                "opaque snapshots changed collector visits at depth {depth}"
            );
            assert_eq!(small.3, large.3, "opaque snapshots changed rewrite work");
        }
    }

    #[test]
    fn integer_match_iota_rewrites_constructor_after_scrutinee_substitution() {
        let scrutinee_variable = Variable(9940);
        let bound_integer = Variable(9941);
        let bound_c = Variable(9942);
        let field_integer = Variable(9943);
        let field_c = Variable(9944);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
            AlgebraicVariantType {
                name: "Empty".into(),
                fields: vec![],
            },
            AlgebraicVariantType {
                name: "Wrapped".into(),
                fields: vec![
                    AlgebraicValueType::Integer,
                    AlgebraicValueType::C(CType::Int32),
                ],
            },
        ]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "Iota".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "Iota".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let constructor = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(field_integer)),
                    AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(field_c))),
                ],
            },
        };
        let body = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Integer(IntegerTerm::var(bound_integer).into()),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(bound_c))),
            ],
        ));
        let input = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(scrutinee_variable),
            }),
            arms: vec![
                AlgebraicIntegerMatchArm {
                    variant: "Empty".into(),
                    bindings: vec![],
                    body: IntegerTerm::constant_i64(0).into(),
                },
                AlgebraicIntegerMatchArm {
                    variant: "Wrapped".into(),
                    bindings: vec![
                        AlgebraicValue::Integer(IntegerTerm::var(bound_integer)),
                        AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(bound_c))),
                    ],
                    body: body.clone().into(),
                },
            ],
        };
        let c_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::new();
        let mut algebraic_replacements = BTreeMap::new();
        algebraic_replacements.insert(scrutinee_variable, constructor.clone());
        let mut rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let output = rewrite.integer(&input);
        let expected = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Integer(IntegerTerm::var(field_integer).into()),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(field_c))),
            ],
        ));
        assert_eq!(output, expected);
        assert!(!matches!(output, IntegerTerm::AlgebraicMatch { .. }));
        assert!(rewrite.changed);

        let malformed_constructor = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(field_integer)),
                    AlgebraicValue::C(CValue::Int64(Bitvector32Term::Variable(field_c))),
                ],
            },
        };
        let mut malformed_replacements = BTreeMap::new();
        malformed_replacements.insert(scrutinee_variable, malformed_constructor);
        let mut malformed_rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &malformed_replacements,
        );
        let malformed_output = malformed_rewrite.integer(&input);
        assert!(matches!(
            malformed_output,
            IntegerTerm::AlgebraicMatch { .. }
        ));

        let mut malformed_input = input.clone();
        let IntegerTerm::AlgebraicMatch { arms, .. } = &mut malformed_input else {
            unreachable!()
        };
        arms[1].bindings[1] = AlgebraicValue::C(CValue::Int32(Bitvector32Term::Add(
            Box::new(Bitvector32Term::Variable(bound_c)),
            Box::new(Bitvector32Term::Constant(1)),
        )));
        let mut malformed_binding_rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let malformed_binding_output = malformed_binding_rewrite.integer(&malformed_input);
        assert!(matches!(
            malformed_binding_output,
            IntegerTerm::AlgebraicMatch { .. }
        ));
    }

    #[test]
    fn typed_integer_iota_consumes_the_shared_budget_before_deep_walk() {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 8,
            smart: 8,
            control: 8,
        };
        let tactic = crate::instrumentation::TacticEvent {
            claim: "integer.typed_iota_budget".into(),
            tactic_index: 0,
            tactic_name: "typed_iota_budget".into(),
            class: "simple".into(),
            statement_index: 0,
            source_index: 0,
        };
        let mut measured_work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let scrutinee_variable = Variable(9960);
            let binding = Variable(9961);
            let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
                name: "Wrapped".into(),
                fields: vec![AlgebraicValueType::Integer],
            }]
            .into();
            let value_type = AlgebraicValueType::Algebraic {
                name: "BudgetMatch".into(),
                arguments: vec![],
            };
            let algebraic_type = AlgebraicType {
                rigid: false,
                name: "BudgetMatch".into(),
                arguments: vec![],
                variants: variants.clone(),
                schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                    value_type, variants,
                )]))),
            };
            let mut body = IntegerTerm::var(binding);
            for _ in 0..depth {
                body = IntegerTerm::Add(body.into(), IntegerTerm::constant_i64(1).into());
            }
            let input = IntegerTerm::AlgebraicMatch {
                scrutinee: Box::new(AlgebraicTerm {
                    algebraic_type: algebraic_type.clone(),
                    node: AlgebraicTermNode::Variable(scrutinee_variable),
                }),
                arms: vec![AlgebraicIntegerMatchArm {
                    variant: "Wrapped".into(),
                    bindings: vec![AlgebraicValue::Integer(IntegerTerm::var(binding))],
                    body: body.into(),
                }],
            };
            let constructor = AlgebraicTerm {
                algebraic_type,
                node: AlgebraicTermNode::Constructor {
                    variant: "Wrapped".into(),
                    fields: vec![AlgebraicValue::Integer(IntegerTerm::constant_i64(7))],
                },
            };
            let c_replacements = BTreeMap::new();
            let integer_replacements = BTreeMap::new();
            let mut algebraic_replacements = BTreeMap::new();
            algebraic_replacements.insert(scrutinee_variable, constructor);
            let ((output, exhausted, visits, work), events) =
                crate::instrumentation::with_tactic_work_limits(limits, || {
                    crate::instrumentation::collect(|| {
                        crate::instrumentation::emit(
                            crate::instrumentation::VerificationEvent::TacticStarted(
                                tactic.clone(),
                            ),
                        );
                        let mut rewrite = TermRewrite::for_typed_variables(
                            &c_replacements,
                            &integer_replacements,
                            &algebraic_replacements,
                        );
                        let (output, work) =
                            crate::instrumentation::measure_deterministic_work(|| {
                                rewrite.integer(&input)
                            });
                        let result = (output, rewrite.integer_work_exhausted, rewrite.visits, work);
                        crate::instrumentation::emit(
                            crate::instrumentation::VerificationEvent::TacticFailed(tactic.clone()),
                        );
                        result
                    })
                });
            assert!(exhausted, "typed iota must consume the enclosing budget");
            assert!(visits <= 16, "typed iota continued after budget exhaustion");
            assert!(work <= 16, "collector work ignored the enclosing budget");
            assert!(matches!(output, IntegerTerm::AlgebraicMatch { .. }));
            assert!(events.iter().any(|event| matches!(
                event,
                crate::instrumentation::VerificationEvent::TacticWorkBudgetExceeded { .. }
            )));
            measured_work.push(work);
        }
        assert!(measured_work.windows(2).all(|pair| pair[1] <= 16));
    }

    #[test]
    fn typed_rewrite_is_simultaneous_across_integer_c_and_algebraic_carriers() {
        let replacement = Variable(9900);
        let integer_source = Variable(9901);
        let c_source = Variable(9902);
        let algebraic_source = Variable(9903);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Unit".into(),
            fields: vec![],
        }]
        .into();
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "TypedRewrite".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                AlgebraicValueType::Algebraic {
                    name: "TypedRewrite".into(),
                    arguments: vec![],
                },
                variants,
            )]))),
        };
        let algebraic_from = AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(algebraic_source),
        };
        let algebraic_to = AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Variable(replacement),
        };
        let mut c_replacements = BTreeMap::new();
        c_replacements.insert(
            c_source,
            TypedCReplacement::Bitvector(Bitvector32Term::Variable(replacement)),
        );
        let mut integer_replacements = BTreeMap::new();
        integer_replacements.insert(integer_source, IntegerTerm::var(replacement));
        integer_replacements.insert(replacement, IntegerTerm::constant_i64(7));
        let mut algebraic_replacements = BTreeMap::new();
        algebraic_replacements.insert(algebraic_source, algebraic_to.clone());
        let body = IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
            "observe".into(),
            vec![
                PureFunctionArgument::Integer(IntegerTerm::var(integer_source).into()),
                PureFunctionArgument::Integer(IntegerTerm::var(replacement).into()),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(c_source))),
                PureFunctionArgument::Algebraic(algebraic_from),
            ],
        ));
        let mut rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let Term::Integer(IntegerTerm::PureFunctionApplication(application)) =
            rewrite.term(&Term::Integer(body))
        else {
            unreachable!()
        };
        assert_eq!(
            application.arguments(),
            &[
                PureFunctionArgument::Integer(IntegerTerm::var(replacement).into()),
                PureFunctionArgument::Integer(IntegerTerm::constant_i64(7).into()),
                PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(replacement))),
                PureFunctionArgument::Algebraic(algebraic_to.clone()),
            ]
        );

        let scoped = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_to.algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(Variable(9904)),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Unit".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::var(replacement))],
                body: IntegerTerm::var(replacement).into(),
            }],
        };
        let mut scoped_rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let Term::Integer(IntegerTerm::AlgebraicMatch { arms, .. }) =
            scoped_rewrite.term(&Term::Integer(scoped))
        else {
            unreachable!()
        };
        let AlgebraicValue::Integer(IntegerTerm::Variable(scoped_binding)) = &arms[0].bindings[0]
        else {
            panic!("Integer match binding was not retained as a variable")
        };
        assert_ne!(*scoped_binding, replacement);
        assert_eq!(
            arms[0].body.as_ref(),
            &IntegerTerm::var(*scoped_binding),
            "the bound occurrence must follow the freshened binder"
        );
    }

    #[test]
    fn integer_fold_rewrite_shared_wrappers_charge_linear_work() {
        let source = Variable(1_040);
        let accumulator = Variable(1_041);
        let item = Variable(1_042);
        let mut samples = Vec::new();
        for depth in [8, 16, 32, 64] {
            let mut common = IntegerTerm::var(Variable(1_043));
            for _ in 0..depth {
                let child: SharedIntegerTerm = common.into();
                common = IntegerTerm::Add(child.clone(), child);
            }
            let shared_body: SharedIntegerTerm = common.into();
            let make_fold = |initial| {
                IntegerTerm::range_fold(
                    crate::kernel::IntegerRangeFoldIndex::Integer {
                        start: IntegerTerm::constant_i64(0).into(),
                        end: IntegerTerm::constant_i64(1).into(),
                    },
                    IntegerTerm::constant_i64(initial),
                    accumulator,
                    item,
                    shared_body.as_ref().clone(),
                )
            };
            let root = IntegerTerm::Add(make_fold(0).into(), make_fold(1).into());
            let renamings = BTreeMap::new();
            let replacement = IntegerTerm::constant_i64(7);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut rewrite =
                    TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
                rewrite.term(&Term::Integer(root))
            });
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 3,
                "shared fold rewrite work grew superlinearly: {samples:?}"
            );
        }
    }

    #[test]
    fn integer_fold_nested_capture_and_nocapture_work_scales_linearly() {
        fn integer_index_fold(
            body: IntegerTerm,
            accumulator: Variable,
            item: Variable,
        ) -> IntegerTerm {
            IntegerTerm::range_fold(
                crate::kernel::IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::constant_i64(1).into(),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                body,
            )
        }

        fn int32_index_fold(
            body: IntegerTerm,
            accumulator: Variable,
            item: Variable,
        ) -> IntegerTerm {
            IntegerTerm::range_fold(
                crate::kernel::IntegerRangeFoldIndex::Int32 {
                    start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(0),
                    ),
                    end: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(1),
                    ),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                body,
            )
        }

        let depths = [8, 16, 32, 64];
        let source = Variable(2_100_000);
        let replacement = IntegerTerm::constant_i64(7);
        let mut nocapture_work = Vec::new();
        for depth in depths {
            let mut nested = IntegerTerm::var(source);
            for level in 0..depth {
                let accumulator = Variable(2_100_100 + level as u64 * 2);
                let item = Variable(2_100_101 + level as u64 * 2);
                nested = integer_index_fold(
                    IntegerTerm::add(nested, IntegerTerm::var(accumulator)),
                    accumulator,
                    item,
                );
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let renamings = BTreeMap::new();
                let mut rewrite =
                    TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
                let result = rewrite.term(&Term::Integer(nested));
                (
                    result,
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                )
            });
            assert!(!result.1 && !result.2);
            let Term::Integer(result) = result.0 else {
                unreachable!()
            };
            let mut free = std::collections::BTreeSet::new();
            crate::kernel::prelude::collect_integer_free_variables(&result, &mut free);
            assert!(!free.contains(&source));
            nocapture_work.push(work);
        }

        let integer_source = Variable(2_101_000);
        let integer_accumulator = Variable(2_101_001);
        let c_item = Variable(2_101_002);
        let mut integer_to_c_work = Vec::new();
        for depth in depths {
            let mut nested = IntegerTerm::var(integer_source);
            for _ in 0..depth {
                nested = int32_index_fold(
                    IntegerTerm::add(nested, IntegerTerm::var(integer_accumulator)),
                    integer_accumulator,
                    c_item,
                );
            }
            let mut integer_to_c_replacement = IntegerTerm::var(integer_accumulator);
            for _ in 0..depth {
                integer_to_c_replacement = IntegerTerm::add(
                    integer_to_c_replacement,
                    IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                        crate::kernel::MachineIntegerType::Int32,
                        Bitvector32Term::Variable(c_item),
                    )),
                );
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let renamings = BTreeMap::new();
                let mut rewrite = TermRewrite::for_integer_variables(
                    integer_source,
                    &integer_to_c_replacement,
                    false,
                    &renamings,
                );
                let result = rewrite.term(&Term::Integer(nested));
                (
                    result,
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                )
            });
            assert!(!result.1 && !result.2);
            let Term::Integer(result) = result.0 else {
                unreachable!()
            };
            let IntegerTerm::RangeFold {
                accumulator: fresh_accumulator,
                item: fresh_item,
                ..
            } = &result
            else {
                unreachable!()
            };
            assert_ne!(*fresh_accumulator, integer_accumulator);
            assert_ne!(*fresh_item, c_item);
            let mut free_integer = std::collections::BTreeSet::new();
            crate::kernel::prelude::collect_integer_free_variables(&result, &mut free_integer);
            assert!(free_integer.contains(&integer_accumulator));
            let mut free_c = std::collections::BTreeSet::new();
            crate::kernel::prelude::collect_integer_capture_bitvector_variables(
                &result,
                &mut free_c,
            );
            assert!(free_c.contains(&c_item));
            integer_to_c_work.push(work);
        }

        let c_source = Variable(2_102_000);
        let c_accumulator = Variable(2_102_001);
        let integer_item = Variable(2_102_002);
        let mut c_to_integer_work = Vec::new();
        for depth in depths {
            let mut nested = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                Bitvector32Term::Variable(c_source),
            ));
            for _ in 0..depth {
                nested = integer_index_fold(
                    IntegerTerm::add(nested, IntegerTerm::var(c_accumulator)),
                    c_accumulator,
                    integer_item,
                );
            }
            let mut replacement_value = IntegerTerm::var(c_accumulator);
            for _ in 0..depth {
                replacement_value =
                    IntegerTerm::add(replacement_value, IntegerTerm::constant_i64(1));
            }
            let c_to_integer_replacement = Bitvector32Term::IntegerToMachine {
                value: SharedIntegerTerm::from(replacement_value),
                destination: crate::kernel::MachineIntegerType::Int32,
            };
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                let source_term = Bitvector32Term::Variable(c_source);
                let mut rewrite = TermRewrite::for_bits(&source_term, &c_to_integer_replacement);
                let result = rewrite.term(&Term::Integer(nested));
                (
                    result,
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                )
            });
            assert!(!result.1 && !result.2);
            let Term::Integer(result) = result.0 else {
                unreachable!()
            };
            let IntegerTerm::RangeFold {
                accumulator: fresh_accumulator,
                ..
            } = &result
            else {
                unreachable!()
            };
            assert_ne!(*fresh_accumulator, c_accumulator);
            let mut free_integer = std::collections::BTreeSet::new();
            crate::kernel::prelude::collect_integer_free_variables(&result, &mut free_integer);
            assert!(free_integer.contains(&c_accumulator));
            c_to_integer_work.push(work);
        }

        for samples in [nocapture_work, integer_to_c_work, c_to_integer_work] {
            for pair in samples.windows(2) {
                assert!(
                    pair[1] <= pair[0] * 4,
                    "nested fold rewrite work grew superlinearly: {samples:?}"
                );
            }
        }
    }

    fn with_checked_simple_budget<R>(limit: usize, operation: impl FnOnce() -> R) -> R {
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: limit,
            smart: limit,
            control: limit,
        };
        let (result, _events) = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                let tactic = crate::instrumentation::TacticEvent {
                    claim: "checked fold collector regression".into(),
                    tactic_index: 0,
                    tactic_name: "checked_fold_collector_regression".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let result = operation();
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                );
                result
            })
        });
        result
    }

    #[test]
    fn checked_machine_rewrite_stops_after_work_exhaustion() {
        let source = Variable(880);
        let mut payload = Bitvector32Term::Variable(source);
        for _ in 0..128 {
            payload =
                Bitvector32Term::Add(Box::new(payload), Box::new(Bitvector32Term::Constant(1)));
        }
        let input = Term::Integer(IntegerTerm::Machine(
            crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                payload,
            ),
        ));
        let (result, _events) = crate::instrumentation::with_tactic_work_limits(
            crate::instrumentation::TacticWorkLimits {
                simple: 4,
                smart: 4,
                control: 4,
            },
            || {
                crate::instrumentation::collect(|| {
                    let tactic = crate::instrumentation::TacticEvent {
                        claim: "checked machine rewrite".into(),
                        tactic_index: 0,
                        tactic_name: "checked_machine_rewrite".into(),
                        class: "simple".into(),
                        statement_index: 0,
                        source_index: 0,
                    };
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                    );
                    let source_term = Bitvector32Term::Variable(source);
                    let replacement = Bitvector32Term::Constant(7);
                    let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement);
                    let output = rewrite.term(&input);
                    let visits = rewrite.visits;
                    let exhausted = rewrite.integer_work_exhausted;
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                    );
                    (output, visits, exhausted)
                })
            },
        );
        assert!(result.2);
        assert!(
            result.1 <= 6,
            "checked rewrite kept traversing after exhaustion: {} visits",
            result.1
        );
    }

    #[test]
    fn checked_rewrite_stops_before_wide_sibling_payloads() {
        let source = Bitvector32Term::Variable(Variable(3_020_000));
        let replacement = Bitvector32Term::Constant(7);
        let input = Term::Bitvector32(Bitvector32Term::PureFunctionApplication {
            name: "wide_checked_payload".into(),
            arguments: vec![source.clone(); 256],
        });
        let (output, visits, exhausted) = with_checked_simple_budget(4, || {
            let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
            let output = rewrite.term(&input);
            (output, rewrite.visits, rewrite.integer_work_exhausted)
        });
        assert!(exhausted);
        assert!(visits <= 8, "rewrite kept visiting siblings: {visits}");
        assert!(matches!(
            output,
            Term::Bitvector32(Bitvector32Term::Constant(0))
        ));
    }

    #[test]
    fn checked_fold_collectors_bound_mixed_carrier_payloads_and_opaque_snapshots() {
        fn integer_index_fold(
            body: IntegerTerm,
            accumulator: Variable,
            item: Variable,
        ) -> IntegerTerm {
            IntegerTerm::range_fold(
                crate::kernel::IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::constant_i64(1).into(),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                body,
            )
        }

        fn int32_index_fold(
            body: IntegerTerm,
            accumulator: Variable,
            item: Variable,
        ) -> IntegerTerm {
            IntegerTerm::range_fold(
                crate::kernel::IntegerRangeFoldIndex::Int32 {
                    start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(0),
                    ),
                    end: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(1),
                    ),
                },
                IntegerTerm::constant_i64(0),
                accumulator,
                item,
                body,
            )
        }

        fn memory_snapshot(depth: usize) -> crate::kernel::SharedCMemory {
            let block = PointerBlock::Concrete("checked-fold-opaque".into());
            let mut memory = CMemory::new().with_block(block.clone(), depth as u32 + 1);
            for offset in 0..depth {
                memory = memory.store(
                    Pointer {
                        block: block.clone(),
                        offset: PointerOffsetTerm::Constant(offset as i64),
                    },
                    CValue::Int32(Bitvector32Term::Constant(offset as u32)),
                );
            }
            crate::kernel::intern_c_memory(memory)
        }

        // Memory snapshots are opaque to lexical collection. Keep the
        // expression and its carrier payload fixed while changing only the
        // snapshot size; the checked rewrite work must stay unchanged.
        let fixed_source = Variable(3_010_000);
        let fixed_accumulator = Variable(3_010_001);
        let fixed_item = Variable(3_010_002);
        let mut fixed_body = IntegerTerm::var(fixed_source);
        for _ in 0..16 {
            fixed_body = int32_index_fold(
                IntegerTerm::add(fixed_body, IntegerTerm::var(fixed_accumulator)),
                fixed_accumulator,
                fixed_item,
            );
        }
        let mut snapshot_work = Vec::new();
        for snapshot_size in [0usize, 256] {
            let memory = memory_snapshot(snapshot_size);
            let pointer = Pointer {
                block: PointerBlock::Concrete("checked-fold-opaque".into()),
                offset: PointerOffsetTerm::Constant(0),
            };
            let replacement_payload = Bitvector32Term::MemoryLoad(memory, Box::new(pointer));
            let replacement =
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    replacement_payload,
                ));
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                with_checked_simple_budget(1_000_000, || {
                    let renamings = BTreeMap::new();
                    let mut rewrite = TermRewrite::for_integer_variables(
                        fixed_source,
                        &replacement,
                        false,
                        &renamings,
                    );
                    let output = rewrite.term(&Term::Integer(fixed_body.clone()));
                    (
                        rewrite.unsupported_integer_scope,
                        rewrite.integer_work_exhausted,
                        output,
                    )
                })
            });
            assert!(!result.0 && !result.1);
            assert!(matches!(result.2, Term::Integer(_)));
            snapshot_work.push(work);
        }
        assert_eq!(snapshot_work[0], snapshot_work[1]);

        let mut integer_to_c_work = Vec::new();
        let mut c_to_integer_work = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let memory = memory_snapshot(depth);
            let pointer = Pointer {
                block: PointerBlock::Concrete("checked-fold-opaque".into()),
                offset: PointerOffsetTerm::Constant(0),
            };
            let integer_source = Variable(3_000_000 + depth as u64);
            let mut int32_body = IntegerTerm::var(integer_source);
            let mut integer_accumulators = Vec::new();
            let mut c_items = Vec::new();
            for level in 0..depth {
                let accumulator = Variable(3_001_000 + level as u64 * 2);
                let item = Variable(3_001_001 + level as u64 * 2);
                integer_accumulators.push(accumulator);
                c_items.push(item);
                int32_body = int32_index_fold(
                    IntegerTerm::add(int32_body, IntegerTerm::var(accumulator)),
                    accumulator,
                    item,
                );
            }
            let integer_capture = *integer_accumulators.last().unwrap();
            let c_capture = *c_items.last().unwrap();
            let mut mixed_c_payload =
                Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer.clone()));
            for _ in 0..depth {
                mixed_c_payload = Bitvector32Term::Add(
                    Box::new(mixed_c_payload),
                    Box::new(Bitvector32Term::IntegerToMachine {
                        value: SharedIntegerTerm::from(IntegerTerm::var(integer_capture)),
                        destination: crate::kernel::MachineIntegerType::Int32,
                    }),
                );
                mixed_c_payload = Bitvector32Term::Add(
                    Box::new(mixed_c_payload),
                    Box::new(Bitvector32Term::Variable(c_capture)),
                );
            }
            let integer_to_c_replacement =
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    mixed_c_payload.clone(),
                ));
            let (result, work, attempts) = {
                let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    with_checked_simple_budget(10, || {
                        let renamings = BTreeMap::new();
                        let mut rewrite = TermRewrite::for_integer_variables(
                            integer_source,
                            &integer_to_c_replacement,
                            false,
                            &renamings,
                        );
                        let output = rewrite.term(&Term::Integer(int32_body.clone()));
                        (rewrite.integer_work_exhausted, output)
                    })
                });
                let attempts = crate::instrumentation::checked_collection_attempts();
                (result, work, attempts)
            };
            assert!(result.0, "low checked budget unexpectedly completed");
            assert!(
                attempts <= 32,
                "collector kept attempting siblings: {attempts}"
            );
            assert!(
                work <= 64,
                "collector kept charging after exhaustion: {work}"
            );

            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                with_checked_simple_budget(1_000_000, || {
                    let renamings = BTreeMap::new();
                    let mut rewrite = TermRewrite::for_integer_variables(
                        integer_source,
                        &integer_to_c_replacement,
                        false,
                        &renamings,
                    );
                    let output = rewrite.term(&Term::Integer(int32_body.clone()));
                    (
                        rewrite.unsupported_integer_scope,
                        rewrite.integer_work_exhausted,
                        output,
                    )
                })
            });
            assert!(!result.0 && !result.1);
            let Term::Integer(output) = result.2 else {
                unreachable!()
            };
            let mut free_c = std::collections::BTreeSet::new();
            crate::kernel::prelude::collect_integer_capture_bitvector_variables(
                &output,
                &mut free_c,
            );
            assert!(!free_c.contains(&integer_source));
            integer_to_c_work.push(work);

            let c_source = Variable(3_002_000 + depth as u64);
            let mut c_to_integer_body =
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    Bitvector32Term::Variable(c_source),
                ));
            let mut math_accumulators = Vec::new();
            let mut mixed_c_items = Vec::new();
            for level in 0..depth {
                if level % 2 == 0 {
                    let accumulator = Variable(3_003_000 + level as u64 * 2);
                    let item = Variable(3_003_001 + level as u64 * 2);
                    math_accumulators.push(accumulator);
                    c_to_integer_body = integer_index_fold(c_to_integer_body, accumulator, item);
                } else {
                    let accumulator = Variable(3_004_000 + level as u64 * 2);
                    let item = Variable(3_004_001 + level as u64 * 2);
                    mixed_c_items.push(item);
                    c_to_integer_body = int32_index_fold(c_to_integer_body, accumulator, item);
                }
            }
            let math_capture = *math_accumulators.last().unwrap();
            let c_item_capture = *mixed_c_items.last().unwrap();
            let mut c_replacement = Bitvector32Term::MemoryLoad(memory, Box::new(pointer));
            for _ in 0..depth {
                c_replacement = Bitvector32Term::Add(
                    Box::new(c_replacement),
                    Box::new(Bitvector32Term::IntegerToMachine {
                        value: SharedIntegerTerm::from(IntegerTerm::var(math_capture)),
                        destination: crate::kernel::MachineIntegerType::Int32,
                    }),
                );
                c_replacement = Bitvector32Term::Add(
                    Box::new(c_replacement),
                    Box::new(Bitvector32Term::Variable(c_item_capture)),
                );
            }
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                with_checked_simple_budget(1_000_000, || {
                    let source = Bitvector32Term::Variable(c_source);
                    let mut rewrite = TermRewrite::for_bits_checked(&source, &c_replacement);
                    let output = rewrite.term(&Term::Integer(c_to_integer_body.clone()));
                    (
                        rewrite.unsupported_integer_scope,
                        rewrite.integer_work_exhausted,
                        output,
                    )
                })
            });
            assert!(!result.0 && !result.1);
            let Term::Integer(output) = result.2 else {
                unreachable!()
            };
            let mut free_c = std::collections::BTreeSet::new();
            crate::kernel::prelude::collect_integer_capture_bitvector_variables(
                &output,
                &mut free_c,
            );
            assert!(!free_c.contains(&c_source));
            c_to_integer_work.push(work);
        }
        for samples in [integer_to_c_work, c_to_integer_work] {
            for pair in samples.windows(2) {
                assert!(
                    pair[1] <= pair[0] * 8 + 64,
                    "checked collector work grew too quickly: {samples:?}"
                );
            }
        }
    }

    #[test]
    fn integer_range_fold_rewrite_rewrites_free_machine_variables_for_integer_index() {
        let binder = Variable(990);
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            Bitvector32Term::Variable(binder),
        ));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
                end: SharedIntegerTerm::from(IntegerTerm::constant_i64(2)),
            },
            IntegerTerm::constant_i64(0),
            Variable(991),
            binder,
            body,
        );
        let from = Bitvector32Term::Variable(binder);
        let to = Bitvector32Term::Constant(7);
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let output = rewrite.term(&Term::Integer(fold));
        let Term::Integer(IntegerTerm::RangeFold { body, .. }) = output else {
            unreachable!()
        };
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Constant(7)));
    }

    #[test]
    fn integer_range_fold_rewrite_keeps_bound_machine_variables_scoped() {
        let binder = Variable(990);
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            Bitvector32Term::Variable(binder),
        ));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    2,
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(991),
            binder,
            body,
        );
        let from = Bitvector32Term::Variable(binder);
        let to = Bitvector32Term::Constant(7);
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let output = rewrite.term(&Term::Integer(fold));
        let Term::Integer(IntegerTerm::RangeFold { item, body, .. }) = output else {
            unreachable!()
        };
        assert_eq!(item, binder);
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(binder)));
    }

    #[test]
    fn integer_range_fold_rewrite_freshens_a_colliding_free_replacement() {
        let binder = Variable(992);
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            Bitvector32Term::Variable(binder),
        ));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Variable(Variable(993)),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Variable(
                    Variable(994),
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(995),
            binder,
            body,
        );
        let from = Bitvector32Term::Variable(Variable(996));
        let to = Bitvector32Term::Variable(binder);
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        let Term::Integer(IntegerTerm::RangeFold { item, body, .. }) =
            rewrite.term(&Term::Integer(fold))
        else {
            unreachable!()
        };
        assert_ne!(item, binder);
        assert!(matches!(body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(item)));
    }

    #[test]
    fn integer_substitution_keeps_integer_source_when_int32_item_reuses_id() {
        let source = Variable(1_020);
        let body = IntegerTerm::Add(
            IntegerTerm::Variable(source).into(),
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                Bitvector32Term::Variable(source),
            ))
            .into(),
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    1,
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(1_021),
            source,
            body,
        );
        let replacement = IntegerTerm::constant_i64(7);
        let renamings = BTreeMap::new();
        let mut rewrite =
            TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
        let Term::Integer(IntegerTerm::RangeFold { item, body, .. }) =
            rewrite.term(&Term::Integer(fold))
        else {
            unreachable!()
        };
        assert_eq!(item, source);
        let IntegerTerm::Add(integer, machine) = body.as_ref() else {
            panic!("source and Int32 item occurrences were not preserved")
        };
        assert!(matches!(integer.as_ref(), IntegerTerm::Constant(value) if value == &7.into()));
        assert!(matches!(machine.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &Bitvector32Term::Variable(source)));
    }

    #[test]
    fn c_substitution_reserves_nested_machine_fold_binders_before_freshening() {
        let source = Variable(1_100);
        let replacement_item = Variable(1_101);
        let nested_item = Variable(1_102);
        let nested_accumulator = Variable(1_103);
        let leaf = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            Bitvector32Term::Variable(source),
        ));
        let nested = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    1,
                )),
            },
            IntegerTerm::constant_i64(0),
            nested_accumulator,
            nested_item,
            leaf,
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    1,
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(1_104),
            replacement_item,
            nested,
        );
        let source_term = Bitvector32Term::Variable(source);
        let replacement = Bitvector32Term::Variable(replacement_item);
        let mut rewrite = TermRewrite::for_bits(&source_term, &replacement);
        let Term::Integer(IntegerTerm::RangeFold { item, body, .. }) =
            rewrite.term(&Term::Integer(fold))
        else {
            unreachable!()
        };
        let IntegerTerm::RangeFold {
            item: retained_item,
            body: retained_body,
            ..
        } = body.as_ref()
        else {
            unreachable!()
        };
        assert_ne!(item, replacement_item);
        assert_ne!(item, nested_item);
        assert_eq!(*retained_item, nested_item);
        assert!(
            matches!(retained_body.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &replacement)
        );
    }

    #[test]
    fn c_substitution_freshens_integer_binder_in_integer_to_machine_replacement() {
        let source = Variable(1_030);
        let accumulator = Variable(1_031);
        let body = IntegerTerm::Add(
            IntegerTerm::Variable(accumulator).into(),
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                Bitvector32Term::Variable(source),
            ))
            .into(),
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            Variable(1_032),
            body,
        );
        let replacement = Bitvector32Term::IntegerToMachine {
            value: SharedIntegerTerm::from(IntegerTerm::Variable(accumulator)),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let source_term = Bitvector32Term::Variable(source);
        let mut rewrite = TermRewrite::for_bits(&source_term, &replacement);
        let Term::Integer(IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            body,
            ..
        }) = rewrite.term(&Term::Integer(fold))
        else {
            unreachable!()
        };
        assert_ne!(fresh_accumulator, accumulator);
        let IntegerTerm::Add(integer, machine) = body.as_ref() else {
            panic!("missing Integer-to-machine replacement")
        };
        assert!(matches!(integer.as_ref(), IntegerTerm::Variable(variable)
            if *variable == fresh_accumulator));
        assert!(matches!(machine.as_ref(), IntegerTerm::Machine(machine)
            if machine.value() == &replacement));
    }

    #[test]
    fn c_substitution_reserves_nested_integer_fold_binders_before_freshening() {
        let source = Variable(1_050);
        let accumulator = Variable(1_051);
        let nested_accumulator = Variable(1_052);
        let nested_item = Variable(1_053);
        let nested_body = IntegerTerm::add(
            IntegerTerm::var(nested_accumulator),
            IntegerTerm::var(nested_item),
        );
        let nested = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            nested_accumulator,
            nested_item,
            nested_body,
        );
        let body = IntegerTerm::add(
            IntegerTerm::var(accumulator),
            IntegerTerm::add(
                nested,
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    Bitvector32Term::Variable(source),
                )),
            ),
        );
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            Variable(1_054),
            body,
        );
        let replacement = Bitvector32Term::IntegerToMachine {
            value: SharedIntegerTerm::from(IntegerTerm::Variable(accumulator)),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let source_term = Bitvector32Term::Variable(source);
        let mut rewrite = TermRewrite::for_bits(&source_term, &replacement);
        let Term::Integer(IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            body,
            ..
        }) = rewrite.term(&Term::Integer(fold))
        else {
            unreachable!()
        };
        assert_ne!(fresh_accumulator, accumulator);
        let IntegerTerm::Add(_, nested_and_machine) = body.as_ref() else {
            panic!("missing nested Integer fold")
        };
        let IntegerTerm::Add(nested, _) = nested_and_machine.as_ref() else {
            panic!("missing nested Integer fold")
        };
        let IntegerTerm::RangeFold {
            accumulator: retained_accumulator,
            item: retained_item,
            ..
        } = nested.as_ref()
        else {
            panic!("nested fold was not retained")
        };
        assert_eq!(*retained_accumulator, nested_accumulator);
        assert_eq!(*retained_item, nested_item);
    }

    #[test]
    fn mixed_fold_and_integer_match_scopes_preserve_carriers() {
        let collision_integer = Variable(3_100_000);
        let collision_c = Variable(3_100_001);
        let integer_source = Variable(3_100_010);
        let c_source = Variable(3_100_011);
        let scrutinee = Variable(3_100_020);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrapped".into(),
            fields: vec![
                AlgebraicValueType::Integer,
                AlgebraicValueType::C(CType::Int32),
            ],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "MixedFoldMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "MixedFoldMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let match_body = || {
            IntegerTerm::Add(
                IntegerTerm::var(integer_source).into(),
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    Bitvector32Term::Variable(c_source),
                ))
                .into(),
            )
        };
        let make_match = || IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(scrutinee),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Wrapped".into(),
                bindings: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(collision_integer)),
                    AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(collision_c))),
                ],
                body: match_body().into(),
            }],
        };
        let c_replacements = BTreeMap::from([(
            c_source,
            TypedCReplacement::Bitvector(Bitvector32Term::Variable(collision_c)),
        )]);
        let integer_replacements =
            BTreeMap::from([(integer_source, IntegerTerm::var(collision_integer))]);
        let algebraic_replacements = BTreeMap::new();

        // A machine-indexed fold contains an Integer-returning match.  Both
        // binders reuse IDs from the replacement's other carrier, so each
        // scope must freshen independently before walking the nested body.
        let fold_with_match = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    1,
                )),
            },
            IntegerTerm::constant_i64(0),
            collision_integer,
            collision_c,
            make_match(),
        );
        let mut rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let Term::Integer(IntegerTerm::RangeFold {
            accumulator,
            item,
            body,
            ..
        }) = rewrite.term(&Term::Integer(fold_with_match))
        else {
            unreachable!()
        };
        assert_ne!(accumulator, collision_integer);
        assert_ne!(item, collision_c);
        let IntegerTerm::AlgebraicMatch { arms, .. } = body.as_ref() else {
            panic!("nested Integer match was not retained")
        };
        let [arm] = arms.as_slice() else {
            unreachable!()
        };
        assert!(matches!(
            &arm.bindings[0],
            AlgebraicValue::Integer(IntegerTerm::Variable(variable)) if *variable != collision_integer
        ));
        assert!(matches!(
            &arm.bindings[1],
            AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(variable)))
                if *variable != collision_c
        ));
        let mut free_integer = BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(
            &IntegerTerm::RangeFold {
                index: crate::kernel::IntegerRangeFoldIndex::Int32 {
                    start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(0),
                    ),
                    end: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(1),
                    ),
                },
                initial: IntegerTerm::constant_i64(0).into(),
                accumulator,
                item,
                body: body.clone(),
            },
            &mut free_integer,
        );
        assert!(free_integer.contains(&collision_integer));
        let mut free_c = BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(
            &IntegerTerm::RangeFold {
                index: crate::kernel::IntegerRangeFoldIndex::Int32 {
                    start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(0),
                    ),
                    end: crate::kernel::SharedIntegerRangeEndpoint::intern(
                        Bitvector32Term::Constant(1),
                    ),
                },
                initial: IntegerTerm::constant_i64(0).into(),
                accumulator,
                item,
                body,
            },
            &mut free_c,
        );
        assert!(free_c.contains(&collision_c));

        // Conversely, an Integer-returning match contains a fold in its arm.
        // This exercises the same carrier maps in the opposite nesting order.
        let match_with_fold = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type,
                node: AlgebraicTermNode::Variable(scrutinee),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Wrapped".into(),
                bindings: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(collision_integer)),
                    AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(collision_c))),
                ],
                body: IntegerTerm::range_fold(
                    crate::kernel::IntegerRangeFoldIndex::Integer {
                        start: IntegerTerm::constant_i64(0).into(),
                        end: IntegerTerm::constant_i64(1).into(),
                    },
                    IntegerTerm::constant_i64(0),
                    collision_integer,
                    collision_c,
                    match_body(),
                )
                .into(),
            }],
        };
        let mut rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewrite.integer(&match_with_fold) else {
            panic!("outer Integer match was not retained")
        };
        let [arm] = arms.as_slice() else {
            unreachable!()
        };
        assert!(matches!(
            &arm.bindings[0],
            AlgebraicValue::Integer(IntegerTerm::Variable(variable)) if *variable != collision_integer
        ));
        assert!(matches!(
            &arm.bindings[1],
            AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(variable)))
                if *variable != collision_c
        ));
        let IntegerTerm::RangeFold {
            accumulator, item, ..
        } = arm.body.as_ref()
        else {
            panic!("nested Integer fold was not retained")
        };
        assert_ne!(*accumulator, collision_integer);
        // The fold item is an Integer carrier here.  A C replacement with
        // the same numeric ID must not force an Integer binder rename.
        assert_eq!(*item, collision_c);
        let mut free_integer = BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(
            arm.body.as_ref(),
            &mut free_integer,
        );
        assert!(free_integer.contains(&collision_integer));
        let mut free_c = BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(
            arm.body.as_ref(),
            &mut free_c,
        );
        assert!(free_c.contains(&collision_c));

        // A typed source may itself be shadowed while another source's
        // replacement mentions that same ID.  The shadowed source must not
        // suppress freshening needed to keep the other replacement free.
        let capture_accumulator = Variable(3_101_000);
        let capture_source = Variable(3_101_001);
        let capture_item = Variable(3_101_002);
        let capture_fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            capture_accumulator,
            capture_item,
            IntegerTerm::var(capture_source),
        );
        let empty_c = BTreeMap::new();
        let capture_integer_replacements = BTreeMap::from([
            (capture_accumulator, IntegerTerm::constant_i64(0)),
            (capture_source, IntegerTerm::var(capture_accumulator)),
        ]);
        let empty_algebraic = BTreeMap::new();
        let mut capture_rewrite = TermRewrite::for_typed_variables(
            &empty_c,
            &capture_integer_replacements,
            &empty_algebraic,
        );
        let Term::Integer(IntegerTerm::RangeFold {
            accumulator, body, ..
        }) = capture_rewrite.term(&Term::Integer(capture_fold))
        else {
            unreachable!()
        };
        assert_ne!(accumulator, capture_accumulator);
        assert!(matches!(
            body.as_ref(),
            IntegerTerm::Variable(variable) if *variable == capture_accumulator
        ));
    }

    #[test]
    fn typed_match_binder_capture_precedes_source_shadowing() {
        let integer_x = Variable(3_102_000);
        let integer_y = Variable(3_102_001);
        let c_x = Variable(3_102_010);
        let c_y = Variable(3_102_011);
        let scrutinee = Variable(3_102_020);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrapped".into(),
            fields: vec![
                AlgebraicValueType::Integer,
                AlgebraicValueType::C(CType::Int32),
            ],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "TypedCaptureMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "TypedCaptureMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let input = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type,
                node: AlgebraicTermNode::Variable(scrutinee),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                variant: "Wrapped".into(),
                bindings: vec![
                    AlgebraicValue::Integer(IntegerTerm::var(integer_x)),
                    AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(c_x))),
                ],
                body: IntegerTerm::PureFunctionApplication(SharedIntegerApplication::intern(
                    "observe_typed_capture".into(),
                    vec![
                        PureFunctionArgument::Integer(IntegerTerm::var(integer_x).into()),
                        PureFunctionArgument::Integer(IntegerTerm::var(integer_y).into()),
                        PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(c_x))),
                        PureFunctionArgument::Value(CValue::Int32(Bitvector32Term::Variable(c_y))),
                    ],
                ))
                .into(),
            }],
        };
        let c_replacements = BTreeMap::from([
            (
                c_x,
                TypedCReplacement::Bitvector(Bitvector32Term::Constant(0)),
            ),
            (
                c_y,
                TypedCReplacement::Bitvector(Bitvector32Term::Variable(c_x)),
            ),
        ]);
        let integer_replacements = BTreeMap::from([
            (integer_x, IntegerTerm::constant_i64(0)),
            (integer_y, IntegerTerm::var(integer_x)),
        ]);
        let algebraic_replacements = BTreeMap::new();
        let mut rewrite = TermRewrite::for_typed_variables(
            &c_replacements,
            &integer_replacements,
            &algebraic_replacements,
        );
        let IntegerTerm::AlgebraicMatch { arms, .. } = rewrite.integer(&input) else {
            panic!("typed match was unexpectedly reduced")
        };
        let [arm] = arms.as_slice() else {
            unreachable!()
        };
        assert!(matches!(
            &arm.bindings[0],
            AlgebraicValue::Integer(IntegerTerm::Variable(variable)) if *variable != integer_x
        ));
        assert!(matches!(
            &arm.bindings[1],
            AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(variable)))
                if *variable != c_x
        ));
        let IntegerTerm::PureFunctionApplication(application) = arm.body.as_ref() else {
            panic!("typed match body changed shape")
        };
        assert!(matches!(
            &application.arguments()[0],
            PureFunctionArgument::Integer(value)
                if matches!(value.as_ref(), IntegerTerm::Variable(variable) if *variable != integer_x)
        ));
        assert!(matches!(
            &application.arguments()[1],
            PureFunctionArgument::Integer(value)
                if matches!(value.as_ref(), IntegerTerm::Variable(variable) if *variable == integer_x)
        ));
        assert!(matches!(
            &application.arguments()[2],
            PureFunctionArgument::Value(CValue::Int32(value))
                if matches!(value, Bitvector32Term::Variable(variable) if *variable != c_x)
        ));
        assert!(matches!(
            &application.arguments()[3],
            PureFunctionArgument::Value(CValue::Int32(value))
                if matches!(value, Bitvector32Term::Variable(variable) if *variable == c_x)
        ));
    }

    #[test]
    fn composite_machine_source_is_rejected_under_c_binder() {
        let source_variable = Variable(3_103_000);
        let source = Bitvector32Term::Add(
            Box::new(Bitvector32Term::Variable(source_variable)),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let replacement = Bitvector32Term::Variable(Variable(3_103_001));
        let fold = IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(
                    Bitvector32Term::Constant(0),
                ),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(
                    1,
                )),
            },
            IntegerTerm::constant_i64(0),
            Variable(3_103_002),
            source_variable,
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                source.clone(),
            )),
        );
        let mut rewrite = TermRewrite::for_bits(&source, &replacement);
        let output = rewrite.term(&Term::Integer(fold));
        assert!(rewrite.unsupported_integer_scope);
        assert!(matches!(
            output,
            Term::Integer(IntegerTerm::Constant(value)) if value == 0.into()
        ));
    }
}
