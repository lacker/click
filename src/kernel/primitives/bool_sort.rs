//! Click `Bool`, the logical sort (`design/machine-integers.md`, Stage 5).
//!
//! A `Bool` term is a [`ConditionTerm`]. `Constant` and `Variable` are its
//! literals and binders, and every comparison is a `Bool` value. Four forms
//! are values that are not comparisons: [`ConditionTerm::BoolApplication`],
//! [`ConditionTerm::BoolIf`], [`ConditionTerm::BoolEqual`] and
//! [`ConditionTerm::BoolLoad`]. This module holds their constructors, the
//! structural helpers every traversal uses for them, and the statements of
//! the logic rules:
//!
//! - **L-If** ([`ConditionTerm::open_bool_if`]):
//!   `ConditionIs(if c { a } else { b }, t)` holds exactly when
//!   `(c and ConditionIs(a, t)) or (not c and ConditionIs(b, t))`. It is
//!   opened only on demand: by a decision of the conditional itself, which
//!   reads its condition first (`PureFactContext::decide_bool_if`), or by a
//!   proof step that asks for the split. Assuming a conditional files it as
//!   one fact; nothing expands it.
//! - **L-Eq** ([`ConditionTerm::bool_equal`]): `ConditionIs(a == b, true)`
//!   holds exactly when `a` and `b` have the same truth. A true one merges
//!   the two values' classes in the e-graph, which then share their truth;
//!   a false one contradicts the merge.
//! - **L-Unfold** ([`ConditionTerm::bool_unfold_equation`]): unfolding a
//!   `-> Bool` function's application files `application == body`.
//!
//! Soundness: these are the two-valued meaning of `if` and of logical
//! equality, and the defining equation of a total pure function, whose
//! termination is checked where it is declared. No rule here reads an
//! integer value of a `Bool`: the sort has none.

use super::{ConditionTerm, Pointer, Proposition, PureFunctionArgument, SharedMemory};
use crate::kernel::SharedPureApplication;

impl ConditionTerm {
    /// Whether this is one of the `Bool` value forms that are not
    /// comparisons. One match on the root.
    pub(crate) fn is_bool_value_form(&self) -> bool {
        matches!(
            self,
            Self::BoolApplication(_)
                | Self::BoolIf { .. }
                | Self::BoolEqual(..)
                | Self::BoolLoad(..)
        )
    }

    /// The application of the `-> Bool` pure function `name`.
    pub(crate) fn bool_application(name: &str, arguments: Vec<PureFunctionArgument>) -> Self {
        Self::BoolApplication(SharedPureApplication::intern(name.to_owned(), arguments))
    }

    /// `if condition { then } else { else }` over `Bool`, folded where its
    /// shape decides it: a constant condition selects its branch, and equal
    /// branches are that branch. Neither fold reads a fact.
    pub(crate) fn bool_if(condition: Self, then_condition: Self, else_condition: Self) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        match condition {
            Self::Constant(true) => then_condition,
            Self::Constant(false) => else_condition,
            condition if then_condition == else_condition => {
                let _ = condition;
                then_condition
            }
            // Rule L-If at constant branches: `if c { true } else { false }`
            // is `c`.
            condition
                if then_condition == Self::Constant(true)
                    && else_condition == Self::Constant(false) =>
            {
                condition
            }
            condition => Self::BoolIf {
                condition: Box::new(condition),
                then_condition: Box::new(then_condition),
                else_condition: Box::new(else_condition),
            },
        }
    }

    /// The logical equality `left == right` of two `Bool` values. A value
    /// is equal to itself, so equal operands fold to `true`.
    pub(crate) fn bool_equal(left: Self, right: Self) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        if left == right {
            return Self::Constant(true);
        }
        Self::BoolEqual(Box::new(left), Box::new(right))
    }

    /// The read of the one-byte `bool` cell at `pointer` in `memory`.
    // Built by the kernel's tests until a front end reads `bool` cells
    // (Stage 5, PR5) or a proof step asks for them.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn bool_load(memory: SharedMemory, pointer: Pointer) -> Self {
        Self::BoolLoad(memory, Box::new(pointer))
    }

    /// Rule L-If: the case split `ConditionIs(self, value)` means, for a
    /// conditional `if c { a } else { b }`:
    /// `(ConditionIs(c, true) and ConditionIs(a, value)) or
    /// (ConditionIs(c, false) and ConditionIs(b, value))`.
    /// `None` for every other condition. It opens one level; the branches
    /// stay as they are, so the work is constant.
    // Built by the kernel's tests until a front end reads `bool` cells
    // (Stage 5, PR5) or a proof step asks for them.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn open_bool_if(&self, value: bool) -> Option<Proposition> {
        let Self::BoolIf {
            condition,
            then_condition,
            else_condition,
        } = self
        else {
            return None;
        };
        crate::instrumentation::record_deterministic_work(1);
        let arm = |selected: bool, branch: &ConditionTerm| {
            Proposition::And(
                Box::new(Proposition::ConditionIs(
                    condition.as_ref().clone(),
                    selected,
                )),
                Box::new(Proposition::ConditionIs(branch.clone(), value)),
            )
        };
        Some(Proposition::Or(
            Box::new(arm(true, then_condition)),
            Box::new(arm(false, else_condition)),
        ))
    }

    /// Rule L-Unfold: the defining equation `application == body` of a
    /// `-> Bool` pure function's application, as the fact unfolding files.
    // Built by the kernel's tests until a front end reads `bool` cells
    // (Stage 5, PR5) or a proof step asks for them.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn bool_unfold_equation(
        application: SharedPureApplication,
        body: Self,
    ) -> Proposition {
        Proposition::ConditionIs(
            Self::BoolEqual(Box::new(Self::BoolApplication(application)), Box::new(body)),
            true,
        )
    }

    /// The child conditions of a `Bool` value form, in order: a
    /// conditional's condition and branches, an equality's operands. Empty
    /// for an application, a read and every other condition.
    pub(crate) fn bool_children(&self) -> impl Iterator<Item = &ConditionTerm> {
        let children: [Option<&ConditionTerm>; 3] = match self {
            Self::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => [Some(condition), Some(then_condition), Some(else_condition)],
            Self::BoolEqual(left, right) => [Some(left), Some(right), None],
            _ => [None, None, None],
        };
        children.into_iter().flatten()
    }

    /// A `Bool` value form rebuilt with `child` applied to each child
    /// condition, `argument` to each argument of an application, and `read`
    /// to a read's state and pointer; `None` for every other condition.
    /// The constructors are the plain nodes, not the folding ones, so a
    /// substitution changes only what it rewrites.
    pub(crate) fn map_bool_value_form(
        &self,
        mut child: impl FnMut(&ConditionTerm) -> ConditionTerm,
        mut argument: impl FnMut(&PureFunctionArgument) -> PureFunctionArgument,
        read: impl FnOnce(&SharedMemory, &Pointer) -> (SharedMemory, Pointer),
    ) -> Option<ConditionTerm> {
        Some(match self {
            Self::BoolApplication(application) => {
                Self::BoolApplication(SharedPureApplication::intern(
                    application.name().to_owned(),
                    application.arguments().iter().map(&mut argument).collect(),
                ))
            }
            Self::BoolIf {
                condition,
                then_condition,
                else_condition,
            } => Self::BoolIf {
                condition: Box::new(child(condition)),
                then_condition: Box::new(child(then_condition)),
                else_condition: Box::new(child(else_condition)),
            },
            Self::BoolEqual(left, right) => {
                Self::BoolEqual(Box::new(child(left)), Box::new(child(right)))
            }
            Self::BoolLoad(memory, pointer) => {
                let (memory, pointer) = read(memory, pointer);
                Self::BoolLoad(memory, Box::new(pointer))
            }
            _ => return None,
        })
    }
}

impl crate::kernel::MachineTerm {
    /// Rule C1: the integer value of the `Bool` `value` at format `to`,
    /// `value as to`. A constant folds to its word, 1 or 0; nothing else is
    /// read.
    pub(crate) fn bool_cast(to: crate::kernel::MachineIntegerType, value: ConditionTerm) -> Self {
        crate::instrumentation::record_deterministic_work(1);
        match value {
            // A constant is the word 1 or 0 at `to`'s carrier.
            ConditionTerm::Constant(value) => {
                crate::kernel::MachineIntegerConstant::from_unsigned(to.format(), u128::from(value))
                    .and_then(|constant| to.constant_term(constant))
                    .expect("every format holds 0 and 1")
            }
            value => Self::BoolCast {
                to,
                value: Box::new(value),
            },
        }
    }

    /// The `Bool` whose integer value this term is (rule C1), or `None`.
    pub(crate) fn bool_cast_operand(&self) -> Option<&ConditionTerm> {
        match self {
            Self::BoolCast { value, .. } => Some(value),
            _ => None,
        }
    }

    /// Rule C1: the integer value at format `to` of the `Bool` a
    /// `ProgramValue::Bool` word carries, `b as to`. A constant word is its own
    /// value, 0 or 1 at every format; a cast is recast at `to`; and any other
    /// word reaches `Bool` by `w != 0` first ([`ConditionTerm::truth_of_bool_word`]).
    pub(crate) fn bool_word_as(to: crate::kernel::MachineIntegerType, word: &Self) -> Self {
        Self::bool_cast(to, ConditionTerm::truth_of_bool_word(word))
    }

    /// The truth a `Bool` constant carrier holds: the `uint8` constant 0 or
    /// 1 (rule C1). `None` for every other term. One match on the root.
    pub(crate) fn bool_constant_value(&self) -> Option<bool> {
        match self {
            Self::Constant {
                format: crate::kernel::MachineIntegerType::UInt8,
                bits,
            } => match bits {
                0 => Some(false),
                1 => Some(true),
                _ => None,
            },
            _ => None,
        }
    }
}

impl ConditionTerm {
    /// The `Bool` a `ProgramValue::Bool` carrier holds. The carrier is 8 bits: a
    /// `Bool` travels as its cast `b as uint8` (rule C1), whose operand is
    /// `b`, or as the `uint8` constant 0 or 1, whose truth it is. Any other
    /// 8-bit term (a variable, a conditional of carriers) reaches `Bool` by
    /// C's test `w != 0` at `uint8`.
    pub(crate) fn truth_of_bool_word(word: &crate::kernel::MachineTerm) -> Self {
        if let Some(value) = word.bool_cast_operand() {
            return value.clone();
        }
        if let Some(value) = word.bool_constant_value() {
            return Self::Constant(value);
        }
        Self::nonzero_bool_word(word)
    }

    /// C's test `w != 0` at `uint8` of a `Bool` carrier, whatever its form:
    /// the truth of any carrier (rule C1), and for a cast `c as uint8`
    /// exactly `c` (rule C1a). One node over the word.
    pub(crate) fn nonzero_bool_word(word: &crate::kernel::MachineTerm) -> Self {
        use crate::kernel::MachineIntegerType;
        Self::bool_not(Self::narrow_compare(
            MachineIntegerType::UInt8,
            crate::kernel::CompareRelation::Equal,
            word.clone(),
            crate::kernel::MachineTerm::bool_cast(MachineIntegerType::UInt8, Self::Constant(false)),
        ))
    }

    /// `not value` as a `Bool` value, the conditional
    /// `if value { false } else { true }` (rule L-If at constant branches).
    /// A constant folds, and a negation's negation is its operand. Nothing
    /// else is read.
    pub(crate) fn bool_not(value: Self) -> Self {
        match value {
            Self::Constant(value) => Self::Constant(!value),
            value => match value.bool_negation_operand() {
                Some(operand) => operand.clone(),
                None => Self::BoolIf {
                    condition: Box::new(value),
                    then_condition: Box::new(Self::Constant(false)),
                    else_condition: Box::new(Self::Constant(true)),
                },
            },
        }
    }

    /// The operand of a negation `not c` ([`ConditionTerm::bool_not`]), or
    /// `None`. One match on the root.
    pub(crate) fn bool_negation_operand(&self) -> Option<&Self> {
        match self {
            Self::BoolIf {
                condition,
                then_condition,
                else_condition,
            } if **then_condition == Self::Constant(false)
                && **else_condition == Self::Constant(true) =>
            {
                Some(condition)
            }
            _ => None,
        }
    }

    /// The claim `ConditionIs(self, value)` with every outer negation read
    /// off, so `not (x == 0)` is filed as `x == 0` at the other polarity
    /// (rule L-If at constant branches). The work is the negation depth.
    pub(crate) fn truth_claim(&self, value: bool) -> Proposition {
        let (mut condition, mut value) = (self, value);
        while let Some(operand) = condition.bool_negation_operand() {
            condition = operand;
            value = !value;
        }
        Proposition::ConditionIs(condition.clone(), value)
    }

    /// Integer to `Bool` (Stage 5): C's conversion of a scalar to `bool`,
    /// the test `value != 0`, or a non-null test for a pointer. It builds no
    /// node beyond the comparison's negation, and is exact for every value:
    /// `(bool)2` and `(bool)-1` are true, with no reduction anywhere. `None`
    /// for a value with no such test (a float, an abstract value).
    pub(crate) fn nonzero_test(value: &crate::kernel::ProgramValue) -> Option<Self> {
        use crate::kernel::{IntegerTerm, MachineIntegerType, MachineTerm, ProgramValue};
        let is_zero = match value.numeric_value() {
            ProgramValue::Bool(word) => return Some(Self::truth_of_bool_word(word)),
            // Rule C1a: a cast is nonzero exactly when its `Bool` holds.
            crate::kernel::integer64_c_value!(word) if word.bool_cast_operand().is_some() => {
                return word.bool_cast_operand().cloned();
            }
            // An 8- or 16-bit integer is tested at its own format.
            narrow @ (ProgramValue::Int8(word)
            | ProgramValue::Int16(word)
            | ProgramValue::UInt8(word)
            | ProgramValue::UInt16(word)) => {
                let format = MachineIntegerType::from_program_type(narrow.program_type())?;
                Self::narrow_compare(
                    format,
                    crate::kernel::CompareRelation::Equal,
                    word.clone(),
                    format.constant_term(crate::kernel::MachineIntegerConstant::from_unsigned(
                        format.format(),
                        0,
                    )?)?,
                )
            }
            ProgramValue::Int32(word) | ProgramValue::UInt32(word) => {
                Self::equal(word.clone(), MachineTerm::constant(0))
            }
            ProgramValue::Int64(word) => {
                Self::int64_equal(word.clone(), MachineTerm::int64_constant(0))
            }
            ProgramValue::UInt64(word) => {
                Self::uint64_equal(word.clone(), MachineTerm::uint64_constant(0))
            }
            value @ (ProgramValue::Int128(word) | ProgramValue::UInt128(word)) => {
                let source = MachineIntegerType::from_program_type(value.program_type())?;
                Self::integer_equal(
                    IntegerTerm::from_machine(source, word.clone())?,
                    IntegerTerm::constant_i64(0),
                )
            }
            ProgramValue::Pointer(pointer) => {
                crate::kernel::eval::pointer_is_null_condition(pointer.pointer().clone())
            }
            _ => return None,
        };
        Some(Self::bool_not(is_zero))
    }
}

impl crate::kernel::ProgramValue {
    /// The `ProgramValue::Bool` carrier of the `Bool` `value`: its cast to
    /// `uint8` (rule C1), the byte a `bool` cell holds.
    pub(crate) fn of_bool(value: ConditionTerm) -> Self {
        Self::Bool(crate::kernel::MachineTerm::bool_cast(
            crate::kernel::MachineIntegerType::UInt8,
            value,
        ))
    }

    /// The C `bool` constant `value`: the `uint8` constant 1 or 0 (rule C1).
    pub(crate) fn bool_constant(value: bool) -> Self {
        Self::of_bool(ConditionTerm::Constant(value))
    }

    /// The scalar value of type `program_type` whose word is `term`; `None` for a
    /// type that is not a scalar.
    pub(crate) fn from_bitvector_term(
        program_type: crate::kernel::ProgramType,
        term: crate::kernel::MachineTerm,
    ) -> Option<Self> {
        use crate::kernel::ProgramType;
        Some(match program_type {
            ProgramType::Bool => Self::Bool(term),
            ProgramType::Int8 => crate::kernel::int8(term),
            ProgramType::Int16 => crate::kernel::int16(term),
            ProgramType::Int32 => Self::Int32(term),
            ProgramType::UInt8 => crate::kernel::uint8(term),
            ProgramType::UInt16 => crate::kernel::uint16(term),
            ProgramType::UInt32 => crate::kernel::uint32(term),
            ProgramType::Int64 => Self::Int64(term),
            ProgramType::UInt64 => Self::UInt64(term),
            ProgramType::Int128 => Self::Int128(term),
            ProgramType::UInt128 => Self::UInt128(term),
            ProgramType::Float32 => Self::Float32(term),
            ProgramType::Float64 => Self::Float64(term),
            _ => return None,
        })
    }
}
