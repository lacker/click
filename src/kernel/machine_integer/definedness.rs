//! Structural adapters between ordinary exact-result bounds and the private
//! overflow queries used by existing interval reasoning. Generated arithmetic
//! domains are ordinary propositions; these adapters never file an opaque
//! overflow fact or alter a lowered term.
//! A single bound identifies a candidate query, but only both bounds establish
//! representability. Unsigned overflow remains wrapping arithmetic.

use super::{FORMATS, Operation, comparison::ComparisonOperand, range, representation};
use crate::kernel::{
    IntegerComparisonOperator, IntegerTerm, MachineIntegerType, MachineOperandView, Proposition,
    SharedIntegerTerm, StoredConditionTerm,
};

/// The formats whose definedness facts the kernel files, narrowest first:
/// those where C arithmetic's overflow is undefined behavior
/// (`representation::files_definedness`).
pub(crate) fn defined_formats() -> impl Iterator<Item = MachineIntegerType> {
    FORMATS
        .into_iter()
        .filter(|ty| representation::files_definedness(*ty))
}

/// The two Integer bounds a definedness fact is exactly equivalent to:
/// `defined(a + b)` on `int32` holds exactly when
/// `to_integer(a) + to_integer(b) <= 2147483647` and
/// `to_integer(a) + to_integer(b) >= -2147483648`, and likewise for `-`
/// and `*` and for every format with an overflow test. A refutation may
/// read the definedness fact as these bounds
/// ([`definedness_of_integer_bound`] checks a listed one).
pub(crate) fn integer_bounds_of_definedness(proposition: &Proposition) -> Vec<Proposition> {
    let Some((format, operation, operands)) = written_nonoverflow(proposition) else {
        return Vec::new();
    };
    bounds_for_operation(format, operation, operands)
        .into_iter()
        .flatten()
        .collect()
}

pub(in crate::kernel) fn bounds_for_operation(
    format: MachineIntegerType,
    operation: Operation,
    operands: [MachineOperandView<'_>; 2],
) -> Option<[Proposition; 2]> {
    Some(ordinary_bounds(
        format,
        exact_result(format, operation, operands)?,
    ))
}

fn exact_result(
    format: MachineIntegerType,
    operation: Operation,
    [left, right]: [MachineOperandView<'_>; 2],
) -> Option<IntegerTerm> {
    Some(operation.exact(left.observe(format)?, right.observe(format)?))
}

pub(crate) fn ordinary_bounds(format: MachineIntegerType, exact: IntegerTerm) -> [Proposition; 2] {
    let exact = SharedIntegerTerm::from(exact);
    let (minimum, maximum) = range::range(format);
    [
        (IntegerComparisonOperator::LessEqual, maximum),
        (IntegerComparisonOperator::GreaterEqual, minimum),
    ]
    .map(|(operator, limit)| {
        let condition = StoredConditionTerm::integer_comparison(
            operator,
            exact.clone(),
            IntegerTerm::constant(limit).into(),
        );
        Proposition::condition_is(condition, true)
    })
}

/// The definedness fact whose Integer bound
/// ([`integer_bounds_of_definedness`]) is exactly `bound`, if any, at a
/// format whose definedness facts are filed ([`defined_formats`]). The
/// candidate is recomputed through the forward map, so only an exact
/// reading is accepted.
pub(crate) fn definedness_of_integer_bound(bound: &Proposition) -> Option<Proposition> {
    overflow_fact_of_integer_bound(bound, defined_formats())
}

/// The fact `not Overflows(F, op, a, b)`, for `F` among `formats`, whose
/// Integer bound ([`integer_bounds_of_definedness`]) is exactly `bound`,
/// if any: the converse of the equivalence, at any format.
pub(crate) fn overflow_fact_of_integer_bound(
    bound: &Proposition,
    formats: impl Iterator<Item = MachineIntegerType>,
) -> Option<Proposition> {
    let query = overflow_query_of_integer_bound(bound, formats)?;
    Some(Proposition::condition_is(query.stored_condition(), false))
}

/// Private query over the original operand handles. Ordinary bounds remain
/// the facts; materializing a legacy condition is a compatibility output only.
#[derive(Clone)]
pub(crate) struct OverflowQueryView {
    pub(crate) format: MachineIntegerType,
    pub(crate) operation: Operation,
    pub(crate) operands: [ComparisonOperand<'static>; 2],
    exact: IntegerTerm,
}

impl OverflowQueryView {
    pub(crate) fn from_operands(
        format: MachineIntegerType,
        operation: Operation,
        operands: [MachineOperandView<'_>; 2],
    ) -> Option<Self> {
        if !representation::has_overflow_test(format) {
            return None;
        }
        let exact = exact_result(format, operation, operands)?;
        Some(Self {
            format,
            operation,
            operands: operands.map(|operand| match operand {
                MachineOperandView::Old(term) => ComparisonOperand::Constant(term.clone()),
                MachineOperandView::Shared(_) => {
                    ComparisonOperand::Observation(operand.retain(format))
                }
            }),
            exact,
        })
    }
    pub(crate) fn operation_kind(&self) -> crate::kernel::OverflowOperation {
        match self.operation {
            Operation::Add => crate::kernel::OverflowOperation::Add,
            Operation::Subtract => crate::kernel::OverflowOperation::Subtract,
            Operation::Multiply => crate::kernel::OverflowOperation::Multiply,
        }
    }

    pub(crate) fn bounds(&self) -> [Proposition; 2] {
        ordinary_bounds(self.format, self.exact.clone())
    }

    fn stored_condition(&self) -> StoredConditionTerm {
        use crate::kernel::MachineOperandView;

        let operands = self.operands.each_ref().map(|operand| {
            if let ComparisonOperand::Observation(machine) = operand
                && machine.retained_written_operand().is_none()
                && let Some(root) = machine.shared_operand()
            {
                return MachineOperandView::Shared(root);
            }
            MachineOperandView::Old(operand.boxed_value())
        });
        StoredConditionTerm::written_overflow(self.format, self.operation_kind(), operands)
    }
}

pub(crate) fn overflow_query_of_integer_bound(
    bound: &Proposition,
    formats: impl Iterator<Item = MachineIntegerType>,
) -> Option<OverflowQueryView> {
    let (_, [first, second]) = written_bound(bound)?;
    let exact = if Operation::of_exact(&first).is_some() {
        first
    } else {
        second
    };
    let (operation, left, right) = Operation::of_exact(&exact)?;
    if !matches!(left, IntegerTerm::Machine(_)) && !matches!(right, IntegerTerm::Machine(_)) {
        return None;
    }
    let carrier =
        |ty: MachineIntegerType, side: &IntegerTerm| -> Option<ComparisonOperand<'static>> {
            match side {
                IntegerTerm::Machine(machine) => {
                    let view = machine.operand_view();
                    if machine.ty().format().bits() == ty.format().bits()
                        && view.observe(ty).as_ref() == Some(side)
                    {
                        return Some(ComparisonOperand::Observation(view.retain(ty)));
                    }
                    let widened = machine.cast_operand(ty);
                    (widened.operand_view().observe(ty).as_ref() == Some(side))
                        .then_some(ComparisonOperand::Observation(widened))
                }
                IntegerTerm::Constant(value) => {
                    range::constant_word(ty, value).map(ComparisonOperand::Constant)
                }
                _ => None,
            }
        };
    formats
        .filter(|ty| representation::has_overflow_test(*ty))
        .find_map(|format| {
            let operands = [carrier(format, left)?, carrier(format, right)?];
            let query = OverflowQueryView {
                format,
                operation,
                operands,
                exact: exact.as_ref().clone(),
            };
            query
                .bounds()
                .iter()
                .any(|expected| same_integer_bound(expected, bound))
                .then_some(query)
        })
}

fn written_bound(
    bound: &Proposition,
) -> Option<(IntegerComparisonOperator, [SharedIntegerTerm; 2])> {
    let Proposition::ConditionIs(condition, true) = bound else {
        return None;
    };
    let comparison = super::comparison::written_integer_comparison(condition.operand_view())?;
    matches!(
        comparison.0,
        IntegerComparisonOperator::LessEqual | IntegerComparisonOperator::GreaterEqual
    )
    .then_some(comparison)
}

/// Same-direction facts use their observation readings (rule W). Mirrored
/// bounds match the original operands in reverse order.
fn same_integer_bound(left: &Proposition, right: &Proposition) -> bool {
    let (Some((a, [x, y])), Some((b, [u, v]))) = (written_bound(left), written_bound(right)) else {
        return left
            .literal_condition()
            .is_some_and(|value| right.literal_condition() == Some(value));
    };
    if a == b {
        x.read_through_ref() == u.read_through_ref() && y.read_through_ref() == v.read_through_ref()
    } else {
        x == v && y == u
    }
}

/// Read one explicitly supplied ordinary range conjunction as an arithmetic
/// query. This is a structural adapter for existing interval certificates;
/// it neither adds an overflow fact nor searches the context for bounds.
pub(crate) fn ordinary_arithmetic_guard(proposition: &Proposition) -> Option<StoredConditionTerm> {
    Some(ordinary_arithmetic_guard_view(proposition)?.stored_condition())
}

pub(crate) fn ordinary_arithmetic_guard_view(
    proposition: &Proposition,
) -> Option<OverflowQueryView> {
    let Proposition::And(first, second) = proposition else {
        return None;
    };
    let query = overflow_query_of_integer_bound(first, defined_formats())?;
    let [upper, lower] = query.bounds();
    ((same_integer_bound(first, &upper) && same_integer_bound(second, &lower))
        || (same_integer_bound(first, &lower) && same_integer_bound(second, &upper)))
    .then_some(query)
}

/// Read a complete ordinary range domain or an explicitly written
/// nonoverflow condition, retaining the operand handles in either case.
pub(crate) fn range_domain_query(proposition: &Proposition) -> Option<OverflowQueryView> {
    ordinary_arithmetic_guard_view(proposition).or_else(|| {
        let (format, operation, operands) = written_nonoverflow(proposition)?;
        OverflowQueryView::from_operands(format, operation, operands)
    })
}

fn written_nonoverflow(
    proposition: &Proposition,
) -> Option<(MachineIntegerType, Operation, [MachineOperandView<'_>; 2])> {
    use crate::kernel::BooleanOperandView;
    let Proposition::ConditionIs(condition, false) = proposition else {
        return None;
    };
    // A native producer may have retained the exact written operands.
    let view = condition
        .root()
        .and_then(|root| root.cached_condition_output())
        .map(BooleanOperandView::Native)
        .unwrap_or_else(|| condition.operand_view());
    let (format, operation, operands) = view.overflow()?;
    let operation = Operation::from_overflow(operation)?;
    if !representation::has_overflow_test(format) {
        return None;
    }
    // Opaque operands retain their written producer or read scope. Some,
    // including conversions of opaque Integer arguments, cannot be retained
    // by the shared machine observation store.
    let operands = if operands.iter().any(|operand| {
        matches!(operand, MachineOperandView::Shared(root)
        if root.has_opaque_observation_boundary() || !root.is_shared_machine_operand())
    }) {
        BooleanOperandView::Native(condition.old_form())
            .overflow()?
            .2
    } else {
        operands
    };
    Some((format, operation, operands))
}

/// Private input form for the existing interval proof rules. Stored facts,
/// obligations and certificate results keep the ordinary propositions. This
/// adapter reads only the explicit proposition, never the ambient context.
pub(crate) fn interval_query_form(proposition: &Proposition) -> Option<Proposition> {
    if let Some(condition) = ordinary_arithmetic_guard(proposition) {
        return Some(Proposition::condition_is(condition, false));
    }
    if let Proposition::And(left, right) = proposition {
        let a = interval_query_form(left);
        let b = interval_query_form(right);
        if a.is_some() || b.is_some() {
            return Some(Proposition::And(
                Box::new(a.unwrap_or_else(|| *left.clone())),
                Box::new(b.unwrap_or_else(|| *right.clone())),
            ));
        }
    }
    None
}

#[cfg(test)]
mod shared_query_tests {
    use super::*;
    use crate::kernel::{OldConditionTerm, OldMachineTerm};

    fn legacy_overflow_query(
        bound: &Proposition,
        formats: impl Iterator<Item = MachineIntegerType>,
    ) -> Option<Proposition> {
        let Some((
            OldConditionTerm::IntegerLessEqual(first, second)
            | OldConditionTerm::IntegerGreaterEqual(first, second),
            true,
        )) = bound.old_condition()
        else {
            return None;
        };
        // The comparison constructors may put the constant on either side.
        let exact = if Operation::of_exact(first).is_some() {
            first
        } else {
            second
        };
        let (_, left, right) = Operation::of_exact(exact)?;
        // An operand is an observation in the operation's format, or a
        // constant, which the forward map produces for a literal operand such
        // as `x + 1`. An `int32` observation of a narrow load or of a widened
        // narrow value reads as the narrow format's
        // (`IntegerTerm::from_machine`), so an operand's word is the one, as
        // written or widened, whose observation in the format gives the
        // operand back.
        let carrier = |ty: MachineIntegerType, side: &IntegerTerm| -> Option<OldMachineTerm> {
            match side {
                IntegerTerm::Machine(machine) => {
                    let word = machine.value().clone();
                    let widened = OldMachineTerm::Cast {
                        spelling: crate::kernel::MachineCastSpelling::Generic,
                        value: Box::new(word.clone()),
                        from: machine.ty(),
                        to: ty,
                    };
                    // A value of another width is never `ty`'s word as written:
                    // its word in `ty` is its widening, a node of its own.
                    let as_written =
                        (machine.ty().format().bits() == ty.format().bits()).then_some(word);
                    as_written.into_iter().chain([widened]).find(|word| {
                        IntegerTerm::from_machine(ty, word.clone()).as_ref() == Some(side)
                    })
                }
                IntegerTerm::Constant(value) => range::constant_word(ty, value),
                _ => None,
            }
        };
        if !matches!(left, IntegerTerm::Machine(_)) && !matches!(right, IntegerTerm::Machine(_)) {
            return None;
        }
        formats
            .filter_map(|ty| {
                let (a, b) = (Box::new(carrier(ty, left)?), Box::new(carrier(ty, right)?));
                Some(Operation::ALL.map(|operation| {
                    representation::overflow_condition(ty, operation, a.clone(), b.clone())
                }))
            })
            .flatten()
            .flatten()
            .find_map(|condition| {
                let fact = Proposition::condition_is(condition, false);
                integer_bounds_of_definedness(&fact)
                    .iter()
                    .any(|expected| same_integer_bound(expected, bound))
                    .then_some(fact)
            })
    }

    #[test]
    fn shared_overflow_queries_preserve_the_legacy_reverse_map() {
        use crate::kernel::{MachineBinaryOp, Variable};
        let _session = crate::kernel::VerificationSession::enter();
        for format in FORMATS {
            let variable = OldMachineTerm::Variable(Variable(982201));
            let words = [
                variable.clone(),
                OldMachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(variable.clone()),
                    right: Box::new(variable.clone()),
                },
                OldMachineTerm::Cast {
                    spelling: crate::kernel::MachineCastSpelling::Generic,
                    from: MachineIntegerType::Int32,
                    to: format,
                    value: Box::new(variable),
                },
            ];
            for word in words {
                let Some(observed) = IntegerTerm::from_machine(format, word) else {
                    continue;
                };
                for operation in Operation::ALL {
                    let exact = operation.exact(observed.clone(), IntegerTerm::constant(1.into()));
                    for bounds_format in FORMATS {
                        let (min, max) = range::range(bounds_format);
                        for bound in [
                            Proposition::condition_is(
                                OldConditionTerm::integer_less_equal(
                                    exact.clone(),
                                    IntegerTerm::constant(max),
                                ),
                                true,
                            ),
                            Proposition::condition_is(
                                OldConditionTerm::integer_greater_equal(
                                    exact.clone(),
                                    IntegerTerm::constant(min),
                                ),
                                true,
                            ),
                        ] {
                            assert_eq!(
                                overflow_fact_of_integer_bound(&bound, FORMATS.into_iter()),
                                legacy_overflow_query(&bound, FORMATS.into_iter()),
                                "{format:?} {operation:?}: {bound:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn explicit_shared_overflow_reads_match_written_bounds_without_exporting() {
        use crate::kernel::{
            KernelTermExport, KernelTermImport, MachineBinaryOp, MachineCastSpelling,
            OverflowOperation, StoredConditionTerm, Variable,
        };
        let _session = crate::kernel::VerificationSession::enter();
        for format in FORMATS {
            let variable = OldMachineTerm::Variable(Variable(982204));
            let words = [
                variable.clone(),
                OldMachineTerm::Binary {
                    format,
                    op: MachineBinaryOp::Add,
                    left: Box::new(variable.clone()),
                    right: Box::new(variable.clone()),
                },
                OldMachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    from: MachineIntegerType::Int32,
                    to: format,
                    value: Box::new(variable),
                },
            ];
            for word in words {
                for op in [
                    OverflowOperation::Add,
                    OverflowOperation::Subtract,
                    OverflowOperation::Multiply,
                    OverflowOperation::Divide,
                    OverflowOperation::ShiftLeft,
                ] {
                    let native = OldConditionTerm::Overflows {
                        format,
                        op,
                        left: Box::new(word.clone()),
                        right: Box::new(range::constant_word(format, &1.into()).unwrap()),
                    };
                    let root = KernelTermImport::for_exact_field_inputs().condition(&native);
                    let stored = StoredConditionTerm::from_root(root.clone()).unwrap();
                    // A native producer can seed the same root's compatibility
                    // cache. Exercise the shared reader before constructing it.
                    let results = [true, false].map(|polarity| {
                        let actual = Proposition::condition_is(stored.clone(), polarity);
                        let before = KernelTermExport::machine_export_count();
                        let bounds = integer_bounds_of_definedness(&actual);
                        let query = range_domain_query(&actual);
                        assert_eq!(KernelTermExport::machine_export_count(), before);
                        assert!(!root.has_cached_native_argument());
                        (polarity, bounds, query)
                    });
                    for (polarity, bounds, query) in results {
                        let expected = Proposition::condition_is(native.clone(), polarity);
                        let expected_bounds = integer_bounds_of_definedness(&expected);
                        let expected_query = range_domain_query(&expected);
                        assert_eq!(bounds, expected_bounds, "{format:?} {op:?} {word:?}");
                        assert_eq!(query.map(|q| q.exact), expected_query.map(|q| q.exact));
                    }
                }
            }
        }
    }

    #[test]
    fn overflow_outputs_preserve_each_integer_address_class() {
        use crate::kernel::effective_type::{CAccessClass, CScalarClass};
        use crate::kernel::{Address, AddressObjectClass, OverflowOperation, Variable};
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::UInt64;
        let classes = [CScalarClass::Int, CScalarClass::Char];
        let outputs = classes.map(|class| {
            let source = Proposition::condition_is(
                OldConditionTerm::Overflows {
                    format,
                    op: OverflowOperation::Add,
                    left: Box::new(OldMachineTerm::IntegerAddress(
                        Box::new(Address::symbolic(Variable(982205))),
                        AddressObjectClass::new(Some(CAccessClass::Scalar(class))),
                    )),
                    right: Box::new(OldMachineTerm::uint64_constant(1)),
                },
                false,
            );
            range_domain_query(&source).unwrap().stored_condition()
        });
        assert_eq!(outputs[0], outputs[1]);
        for (output, class) in outputs.iter().zip(classes) {
            let OldConditionTerm::Overflows { left, .. } = output.old_form() else {
                unreachable!()
            };
            let OldMachineTerm::IntegerAddress(_, annotation) = &**left else {
                unreachable!()
            };
            assert_eq!(annotation.class(), Some(CAccessClass::Scalar(class)));
        }
    }

    mod scaling_tests {
        include!("../../scaling_tests/kernel/machine_integer/definedness/tests.rs");
    }
}
