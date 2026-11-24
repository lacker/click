//! In-range identity: `to_integer(a op b) == to_integer(a) op to_integer(b)`
//! for a machine `+`, `-` or `*` of format `F` whose exact result lies in
//! `F`.
//!
//! The machine operation is the exact result reduced modulo `2^w` into
//! `F`: each operand's word is congruent to its value modulo `2^w`
//! (a narrow value's word is its canonical extension, congruent modulo
//! `2^32` and so modulo its own `2^w`), and `+`, `-` and `*` respect the
//! congruence. When the exact result lies in `F` it is the one element of
//! `F` in its residue class, so it is the machine result. The certificate
//! rule `integer_operation_identity` and the root-local `close()` rule check
//! this statement for the observation's format using its exact range pair.
//! The latter accepts only a written operation, without memory resolution.

use super::{Operation, definedness, range, representation};
#[cfg(test)]
use crate::kernel::MachineTerm;
use crate::kernel::{
    ConditionTerm, IntegerTerm, MachineIntegerType, Proposition, SharedMachineIntegerTerm,
};
use num_bigint::BigInt;

/// The format of the machine `+`, `-` or `*` that `observed` reads, and
/// its exact value spelled over the operands' own observations in that
/// format. `to_integer(observed) == value` is the in-range identity once
/// `value` is bounded inside the format.
pub(crate) fn mathematical(observed: &IntegerTerm) -> Option<(MachineIntegerType, IntegerTerm)> {
    mathematical_operation(observed).map(|(_, ty, exact)| (ty, exact))
}

/// The written operator only. Checking a known identity must not recover
/// an operation by resolving a read or walking memory history.
pub(crate) fn explicit_mathematical(
    observed: &IntegerTerm,
) -> Option<(MachineIntegerType, IntegerTerm)> {
    let IntegerTerm::Machine(machine) = observed.value_read() else {
        return None;
    };
    let ty = machine.ty();
    let (operation, [left, right]) = representation::view_operation(ty, machine.operand_view())?;
    Some((ty, operation.exact(left.observe(ty)?, right.observe(ty)?)))
}

fn mathematical_operation(
    observed: &IntegerTerm,
) -> Option<(Operation, MachineIntegerType, IntegerTerm)> {
    // An observation of σ or a widening of the operation is read through
    // its value relation (rule W) to the operation's own observation.
    let IntegerTerm::Machine(machine) = observed.value_read() else {
        return None;
    };
    let ty = machine.ty();
    // An explicit operation's identity refers to its actual operands. Only
    // an observation of a stored read needs the read-over-write adapter;
    // recursively expanding an explicit operation changes the identity the
    // source expression asks for.
    let view = machine.operand_view();
    if let Some((operation, [left, right])) = representation::view_operation(ty, view) {
        return Some((
            operation,
            ty,
            operation.exact(left.observe(ty)?, right.observe(ty)?),
        ));
    }
    let source = view.read_source()?;
    let resolved = crate::kernel::eval::read_over_write_value(&source)?;
    let (operation, left, right) = representation::word_operation(ty, &resolved)?;
    let left = IntegerTerm::from_machine(ty, left.clone())?;
    let right = IntegerTerm::from_machine(ty, right.clone())?;
    Some((operation, ty, operation.exact(left, right)))
}

/// Whether `stated` is the exact value `value` of an operation
/// ([`mathematical`]) up to the value relations of its operands' observations
/// (rule W): the same operation over operands with one value reading each,
/// `to_integer(tag) + to_integer(p0 as uint32)` for the observation of
/// `tag + p0` at `uint32`. O(1): one root match and two readings per side.
pub(crate) fn same_exact_value(value: &IntegerTerm, stated: &IntegerTerm) -> bool {
    if value == stated {
        return true;
    }
    match (Operation::of_exact(value), Operation::of_exact(stated)) {
        (Some((operation, left, right)), Some((stated_operation, stated_left, stated_right))) => {
            operation == stated_operation
                && left.value_read() == stated_left.value_read()
                && right.value_read() == stated_right.value_read()
        }
        _ => false,
    }
}

/// [`mathematical`] for `+` and `-` only: the operations whose identity
/// the comparison readings and the surface's identity planner spell.
pub(crate) fn additive_mathematical(
    observed: &IntegerTerm,
) -> Option<(MachineIntegerType, IntegerTerm)> {
    let (op, ty, exact) = mathematical_operation(observed)?;
    matches!(op, Operation::Add | Operation::Subtract).then_some((ty, exact))
}

/// One endpoint of a format's range that the exact value of a machine
/// `+` or `-` must respect for the operation to equal that value: `exact
/// >= bound` when `lower`, else `exact <= bound`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntegerOperationRangeBound {
    pub(crate) exact: IntegerTerm,
    pub(crate) bound: BigInt,
    pub(crate) lower: bool,
}

impl IntegerOperationRangeBound {
    /// Ordinary spellings of this bound. Legacy overflow evidence is selected
    /// through `overflow_query`, retaining its exact source rather than
    /// manufacturing a boxed predicate as a lookup key.
    pub(crate) fn stating_facts(&self) -> Vec<Proposition> {
        let bound = IntegerTerm::constant(self.bound.clone());
        let forms = if self.lower {
            [
                ConditionTerm::integer_greater_equal(self.exact.clone(), bound.clone()),
                ConditionTerm::integer_less_equal(bound, self.exact.clone()),
            ]
        } else {
            [
                ConditionTerm::integer_less_equal(self.exact.clone(), bound.clone()),
                ConditionTerm::integer_greater_equal(bound, self.exact.clone()),
            ]
        };
        let mut facts = forms
            .into_iter()
            .map(|form| Proposition::condition_is(form, true))
            .collect::<Vec<_>>();
        // 0 <= (x - y) is exactly y <= x. Retain a comparison view
        // when both observations have the same format, so a direct machine
        // bound can certify subtraction without a difference-graph walk.
        if self.lower
            && self.bound == BigInt::from(0)
            && let IntegerTerm::Subtract(left, right) = &self.exact
            && let (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) =
                (left.as_ref(), right.as_ref())
            && left.ty() == right.ty()
        {
            use super::comparison::{ComparisonOperand, NativeComparisonView};
            facts.push(
                NativeComparisonView {
                    format: left.ty(),
                    relation: super::Relation::LessEqual,
                    operands: [
                        ComparisonOperand::Observation(right.clone()),
                        ComparisonOperand::Observation(left.clone()),
                    ],
                }
                .integer_proposition(),
            );
        }
        facts
    }
    pub(crate) fn overflow_query(&self) -> Option<definedness::OverflowQueryView> {
        self.stating_facts().iter().find_map(|fact| {
            definedness::overflow_query_of_integer_bound(fact, definedness::defined_formats())
        })
    }
}

/// The exact observation of the machine `+` or `-` in `ty` whose
/// mathematical value ([`mathematical`]) is `exact`, an Integer sum or
/// difference of observations and constants, with the range bounds the
/// operation must respect to equal it. A bound the operands' own ranges
/// already imply is not listed: `4294967295 - to_integer(b)` for `uint32`
/// `b` lies in `uint32` and needs none. The candidate is recomputed through
/// the forward map, so only an exact reading is returned.
pub(crate) fn machine_operation_of_integer_value(
    exact: &IntegerTerm,
    ty: MachineIntegerType,
) -> Option<(IntegerTerm, Vec<IntegerOperationRangeBound>)> {
    let (operation, left, right) = match Operation::of_exact(exact)? {
        found @ (Operation::Add | Operation::Subtract, _, _) => found,
        (Operation::Multiply, _, _) => return None,
    };
    // An operand's word is the one, as written or widened, whose
    // observation in `ty` gives the operand back; its range is its own
    // format's, or the constant itself.
    let operand = |side: &IntegerTerm| -> Option<(SharedMachineIntegerTerm, BigInt, BigInt)> {
        // An observation is read through its value relations (rule W): the
        // range of `to_integer(x as uint32)` is `x`'s own format's.
        match side.value_read() {
            IntegerTerm::Machine(machine) => {
                if machine.ty() == ty {
                    let (low, high) = range::range(ty);
                    return Some((machine.clone(), low, high));
                }
                let (low, high) = range::range(machine.ty());
                if machine.ty().format().bits() == ty.format().bits()
                    && machine
                        .operand_view()
                        .observe(ty)
                        .is_some_and(|observed| observed.value_read() == side.value_read())
                {
                    return Some((machine.operand_view().retain(ty), low, high));
                }
                let widened = machine.cast_operand(ty);
                widened
                    .operand_view()
                    .observe(ty)
                    .filter(|observed| observed.value_read() == side.value_read())?;
                Some((widened, low, high))
            }
            IntegerTerm::Constant(value) => Some((
                SharedMachineIntegerTerm::intern(ty, range::constant_word(ty, value)?),
                value.clone(),
                value.clone(),
            )),
            _ => None,
        }
    };
    let (left_word, left_low, left_high) = operand(left)?;
    let (right_word, right_low, right_high) = operand(right)?;
    let observed = representation::operation_observation(ty, operation, &left_word, &right_word)?;
    let (read_ty, value) = mathematical(&observed)?;
    if read_ty != ty || !same_exact_value(&value, exact) {
        return None;
    }
    let (low, high) = if operation == Operation::Subtract {
        (left_low - right_high, left_high - right_low)
    } else {
        (left_low + right_low, left_high + right_high)
    };
    let (minimum, maximum) = range::range(ty);
    let mut bounds = Vec::new();
    if low < minimum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: minimum,
            lower: true,
        });
    }
    if high > maximum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: maximum,
            lower: false,
        });
    }
    Some((observed, bounds))
}

#[test]
fn explicit_operation_identity_keeps_its_read_operands() {
    use crate::kernel::{Address, LoadKind, ProgramValue, SymbolicMemory, Variable};
    let _session = crate::kernel::VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let x = MachineTerm::Variable(Variable(989_773));
    let y = MachineTerm::Variable(Variable(989_774));
    let address = Address::symbolic(Variable(989_775));
    let stored = MachineTerm::logical_machine_binary(
        format,
        crate::kernel::MachineBinaryOp::Add,
        x.clone(),
        MachineTerm::constant(1),
    );
    let memory = SymbolicMemory::new().store(address.clone(), ProgramValue::Int32(stored));
    let read = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_memory_ref(&memory),
        address,
        LoadKind::Int32,
    );
    let observe = |value| IntegerTerm::from_machine(format, value).unwrap();
    let sum = observe(MachineTerm::logical_machine_binary(
        format,
        crate::kernel::MachineBinaryOp::Add,
        read.clone(),
        y.clone(),
    ));
    assert_eq!(
        mathematical(&sum),
        Some((format, IntegerTerm::add(observe(read.clone()), observe(y))))
    );
    assert_eq!(
        mathematical(&observe(read)),
        Some((
            format,
            IntegerTerm::add(observe(x), IntegerTerm::constant(1.into()))
        ))
    );
}

#[cfg(test)]
fn boxed_machine_operation_of_integer_value(
    exact: &IntegerTerm,
    ty: MachineIntegerType,
) -> Option<(IntegerTerm, Vec<IntegerOperationRangeBound>)> {
    let (operation, left, right) = match Operation::of_exact(exact)? {
        found @ (Operation::Add | Operation::Subtract, _, _) => found,
        (Operation::Multiply, _, _) => return None,
    };
    // An operand's word is the one, as written or widened, whose
    // observation in `ty` gives the operand back; its range is its own
    // format's, or the constant itself.
    let operand = |side: &IntegerTerm| -> Option<(MachineTerm, BigInt, BigInt)> {
        // An observation is read through its value relations (rule W): the
        // range of `to_integer(x as uint32)` is `x`'s own format's.
        match side.value_read() {
            IntegerTerm::Machine(machine) => {
                let word = machine.value().clone();
                // A 32-to-64-bit extension is its typed node, its one
                // spelling; every other widening is a generic node.
                let widened = if super::conversion::extension_encoding(machine.ty(), ty).is_some() {
                    super::conversion::convert_term(machine.ty(), ty, word.clone())
                } else {
                    MachineTerm::Cast {
                        spelling: crate::kernel::MachineCastSpelling::Generic,
                        value: Box::new(word.clone()),
                        from: machine.ty(),
                        to: ty,
                    }
                };
                // A value of another width is never `ty`'s word as written:
                // its word in `ty` is its widening, a node of its own.
                let as_written =
                    (machine.ty().format().bits() == ty.format().bits()).then_some(word);
                let word = as_written.into_iter().chain([widened]).find(|word| {
                    IntegerTerm::from_machine(ty, word.clone())
                        .is_some_and(|observed| observed.value_read() == side.value_read())
                })?;
                let (low, high) = range::range(machine.ty());
                Some((word, low, high))
            }
            IntegerTerm::Constant(value) => Some((
                range::constant_word(ty, value)?,
                value.clone(),
                value.clone(),
            )),
            _ => None,
        }
    };
    let (left_word, left_low, left_high) = operand(left)?;
    let (right_word, right_low, right_high) = operand(right)?;
    let word =
        representation::operation_word(ty, operation, Box::new(left_word), Box::new(right_word))?;
    let observed = IntegerTerm::from_machine(ty, word)?;
    let (read_ty, value) = mathematical(&observed)?;
    if read_ty != ty || !same_exact_value(&value, exact) {
        return None;
    }
    let (low, high) = if operation == Operation::Subtract {
        (left_low - right_high, left_high - right_low)
    } else {
        (left_low + right_low, left_high + right_high)
    };
    let (minimum, maximum) = range::range(ty);
    let mut bounds = Vec::new();
    if low < minimum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: minimum,
            lower: true,
        });
    }
    if high > maximum {
        bounds.push(IntegerOperationRangeBound {
            exact: exact.clone(),
            bound: maximum,
            lower: false,
        });
    }
    Some((observed, bounds))
}

#[test]
fn inverse_operation_mapping_matches_boxed_conversion_routes() {
    use crate::kernel::{KernelTermExport, Variable};
    let _session = crate::kernel::VerificationSession::enter();
    for source in super::FORMATS {
        let value =
            IntegerTerm::from_machine(source, MachineTerm::Variable(Variable(989781))).unwrap();
        for target in super::FORMATS {
            for rhs in [
                value.clone(),
                IntegerTerm::constant(1.into()),
                IntegerTerm::constant((-1).into()),
                IntegerTerm::from_machine(
                    source,
                    MachineTerm::IntegerToMachine {
                        value: IntegerTerm::Variable(Variable(989782)).into(),
                        destination: source,
                    },
                )
                .unwrap(),
            ] {
                for exact in [
                    IntegerTerm::Add(value.clone().into(), rhs.clone().into()),
                    IntegerTerm::Subtract(value.clone().into(), rhs.into()),
                ] {
                    let old = boxed_machine_operation_of_integer_value(&exact, target);
                    let new = machine_operation_of_integer_value(&exact, target);
                    assert_eq!(
                        new.is_some(),
                        old.is_some(),
                        "{source:?} -> {target:?}: {exact:?}"
                    );
                    if let (Some((new, bounds)), Some((old, old_bounds))) = (new, old) {
                        assert_eq!(bounds, old_bounds);
                        let IntegerTerm::Machine(new) = new else {
                            panic!("machine operation")
                        };
                        let IntegerTerm::Machine(old) = old else {
                            panic!("machine operation")
                        };
                        let new_word = new
                            .shared_operand()
                            .map(KernelTermExport::machine)
                            .transpose()
                            .unwrap();
                        assert_eq!(
                            new_word.as_ref().unwrap_or_else(|| new.value()),
                            old.value()
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn inverse_operation_mapping_preserves_constant_operation_structure() {
    use crate::kernel::{KernelTerm, KernelTermImport, MachineBinaryOp};
    let _session = crate::kernel::VerificationSession::enter();
    for ty in super::FORMATS {
        for a in [-1, 0, 1, 127, 255] {
            for b in [-1, 0, 1] {
                let exact = IntegerTerm::Add(
                    IntegerTerm::constant(a.into()).into(),
                    IntegerTerm::constant(b.into()).into(),
                );
                assert_eq!(
                    machine_operation_of_integer_value(&exact, ty),
                    boxed_machine_operation_of_integer_value(&exact, ty)
                );
            }
        }
        if representation::word_bits(ty).is_some() {
            let literal = KernelTermImport::default()
                .machine_arithmetic(ty, &range::constant_word(ty, &1.into()).unwrap())
                .unwrap();
            let root = KernelTerm::machine_binary_shared(
                ty,
                MachineBinaryOp::Add,
                [literal.clone(), literal],
            );
            let observed =
                IntegerTerm::Machine(SharedMachineIntegerTerm::from_shared(ty, root).unwrap());
            let exact = IntegerTerm::Add(observed.into(), IntegerTerm::constant(1.into()).into());
            assert_eq!(
                machine_operation_of_integer_value(&exact, ty),
                boxed_machine_operation_of_integer_value(&exact, ty)
            );
        }
    }
}

#[test]
fn shared_operation_bounds_keep_legacy_overflow_authority_without_export() {
    use crate::kernel::{
        KernelTermImport, MachineBinaryOp, OverflowOperation, PureFactContext, Variable,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let written = MachineTerm::Binary {
        format,
        op: MachineBinaryOp::Add,
        left: Box::new(MachineTerm::Variable(Variable(989798))),
        right: Box::new(MachineTerm::Variable(Variable(989799))),
    };
    let operand = SharedMachineIntegerTerm::from_shared(
        format,
        KernelTermImport::default()
            .machine_arithmetic(format, &written)
            .unwrap(),
    )
    .unwrap();
    let bound = IntegerOperationRangeBound {
        exact: Operation::Add.exact(
            IntegerTerm::Machine(operand.clone()),
            IntegerTerm::constant(2.into()),
        ),
        bound: i32::MAX.into(),
        lower: false,
    };
    let source = Proposition::condition_is(
        ConditionTerm::Overflows {
            format,
            op: OverflowOperation::Add,
            left: Box::new(written),
            right: Box::new(MachineTerm::constant(2)),
        },
        false,
    );
    let parent = PureFactContext::new();
    let child = parent.clone().assume_proposition(source.clone());
    assert!(child.knows_operation_range_bound(&bound));
    assert!(!parent.knows_operation_range_bound(&bound));
    assert!(!operand.has_boxed_operand());
}
