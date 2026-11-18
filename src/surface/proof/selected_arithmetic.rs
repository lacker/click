//! `solve` on an `Integer` fact whose atoms observe machine values.
//!
//! Selected-premise arithmetic reads linear `Integer` claims. A proof about `to_integer(i)`
//! usually also needs what the program knows about `i` itself: `i < n` for
//! two `uint64` values says `to_integer(i) < to_integer(n)`, and a `uint64`
//! is never negative. Those facts reach that arithmetic as the steps a proof would
//! write by hand: each connected machine order fact is carried to `Integer`
//! by `known` (a comparison of observations is the native comparison),
//! and each unsigned value's observation gets its type range by `known()`.
//! Planning uses the original and carried facts, retaining only the bridges
//! the resulting proof needs. Expansion writes ordinary Integer law
//! applications, explicit range proofs, and `known()` observation identities;
//! legacy certificate routes remain for unmigrated forms. Planning is untrusted.

use super::wide_arithmetic::{
    Carrier, Relation, have, operation_identity, relate, relation_parts, to_integer, type_range,
};
use super::*;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::surface::checking::{IntegerRefutation, refute_integer_goal};

// Arithmetic subgoals reuse the outer memory search. Nested arithmetic
// scopes preserve that choice until the outermost bridge returns.
thread_local! {
    static ACTIVE_MACHINE_EQUALITY_BRIDGE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

pub(super) fn machine_equality_bridge_active() -> bool {
    ACTIVE_MACHINE_EQUALITY_BRIDGE.with(std::cell::Cell::get)
}

struct MachineEqualityBridgeScope {
    previous: bool,
}

impl MachineEqualityBridgeScope {
    fn enter() -> Self {
        Self {
            previous: ACTIVE_MACHINE_EQUALITY_BRIDGE.with(|active| active.replace(true)),
        }
    }
}

impl Drop for MachineEqualityBridgeScope {
    fn drop(&mut self) {
        ACTIVE_MACHINE_EQUALITY_BRIDGE.with(|active| active.set(self.previous));
    }
}

/// How many rewrites `solve`'s connected-equality chain takes before closing.
const REWRITE_DEPTH: usize = 3;

/// How many connected equalities the search offers, and how many checked
/// rewrites it tries in all. A large connected component fails promptly
/// instead of exploring every short chain of its equalities.
const REWRITE_EQUALITIES: usize = 64;
const REWRITE_ATTEMPTS: usize = 256;

/// How many rewritten goals the search offers to `solve`, after the cheap
/// closers miss: `solve` unfolds and computes what a rewrite exposes.
const REWRITE_SOLVE_CLOSURES: usize = 8;

/// How many rewrites `solve`'s single-rewrite strategy tries, each followed
/// by `known`: a goal that restates a fact through one equation.
const SINGLE_REWRITES: usize = 16;

/// How many connected constructor equations `solve` pairs.
const CONSTRUCTOR_EQUATIONS: usize = 16;

/// How many connected function facts `solve` reads a goal out of, and how
/// many leaves of one definition's conditional tree it splits down to.
const DEFINITION_FACTS: usize = 16;
const DEFINITION_LEAVES: usize = 16;
/// How many applications at a definition's ends `solve` follows into their
/// own definitions on the way to one end.
const DEFINITION_UNFOLDS: usize = 4;

/// The machine type an order fact compares.
#[derive(Clone, Copy, Eq, PartialEq)]
enum MachineOrder {
    Int32,
    Wide(Carrier),
    /// A 64-bit equality. The kernel's equality does not say whether its
    /// operands are signed, so its bridges are tried for `uint64` and then
    /// `int64`; the other type's application is refused.
    Equal64,
}

impl MachineOrder {
    fn of(proposition: &Proposition) -> Option<Self> {
        if let Some(carrier) = Carrier::of(proposition) {
            return Some(Self::Wide(carrier));
        }
        match proposition {
            condition_source_0 @ Proposition::ConditionIs(_, _)
                if let Some((
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        ..
                    }
                    | ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        ..
                    },
                    _,
                )) = condition_source_0.condition_native() =>
            {
                Some(Self::Int32)
            }
            // An `int32` equality; a `uint32` one is refused by the `int32`
            // bridges and left out.
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                        relation: CompareRelation::Equal,
                        ..
                    },
                    _,
                )) = condition_source_0.condition_native() =>
            {
                Some(Self::Int32)
            }
            condition_source_0 @ Proposition::ConditionIs(_, true)
                if let Some((
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        ..
                    },
                    _,
                )) = condition_source_0.condition_native() =>
            {
                Some(Self::Equal64)
            }
            _ => None,
        }
    }

    fn typed_literals(self, expression: &ContractExpression) -> ContractExpression {
        match self {
            Self::Int32 | Self::Equal64 => expression.clone(),
            Self::Wide(carrier) => carrier.typed_literals(expression),
        }
    }

    /// The type range of a value's observation, as Integer literals, for
    /// the types a carried order reads ranges of.
    fn range(self) -> Option<(String, String)> {
        let ty = match self {
            Self::Int32 => crate::kernel::MachineIntegerType::Int32,
            Self::Wide(carrier) => carrier.machine_type(),
            Self::Equal64 => return None,
        };
        let (minimum, maximum) = crate::kernel::machine_integer::range::range(ty);
        Some((minimum.to_string(), maximum.to_string()))
    }
}

/// One carried fact: how it is established and its source spelling.
struct Carried {
    establish: Establish,
    surface: ClickProposition,
}

enum Establish {
    /// A fixed sequence of steps.
    Steps(Vec<ProofStep>),
    /// The term-by-term observation of `left + right` or `left - right`:
    /// a signed operation once it is defined, which `solve` proves when it is
    /// not already a fact, and an unsigned one once it stays in range.
    Operation {
        operation: ContractExpression,
        left: ContractExpression,
        right: ContractExpression,
        subtract: bool,
        /// The operation's machine format.
        format: crate::kernel::MachineIntegerFormat,
    },
}

/// The format of the machine `+` or `-` whose observation an identity
/// `to_integer(a op b) == to_integer(a) op to_integer(b)` states.
fn observed_operation_format(
    identity: &Proposition,
) -> Option<crate::kernel::MachineIntegerFormat> {
    let Some((ConditionTerm::IntegerEqual(left, right), true)) = identity.condition_native() else {
        return None;
    };
    [left, right].into_iter().find_map(|side| {
        crate::kernel::machine_integer::identity::additive_mathematical(side)
            .map(|(ty, _)| ty.format())
    })
}

#[cfg(test)]
thread_local! {
    static BRIDGE_ESTABLISHMENTS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

thread_local! {
    // A bridge may ask for this operation's definedness or no-wrap bound.
    // Proving that prerequisite can find the same operation among connected
    // machine facts. Re-entering its bridge cannot establish new evidence.
    static ACTIVE_OPERATION_BRIDGES: std::cell::RefCell<Vec<ContractExpression>> = const { std::cell::RefCell::new(Vec::new()) };
}

struct OperationBridgeScope;

impl OperationBridgeScope {
    fn enter(operation: &ContractExpression) -> Option<Self> {
        ACTIVE_OPERATION_BRIDGES.with(|active| {
            let mut active = active.borrow_mut();
            if active.contains(operation) {
                return None;
            }
            active.push(operation.clone());
            Some(Self)
        })
    }
}

impl Drop for OperationBridgeScope {
    fn drop(&mut self) {
        ACTIVE_OPERATION_BRIDGES.with(|active| {
            active.borrow_mut().pop();
        });
    }
}

/// The type range of the observation of `value`, a machine value of
/// `format`.
fn range_items(
    value: &ContractExpression,
    format: crate::kernel::MachineIntegerFormat,
) -> Vec<Carried> {
    let (minimum, maximum) = format.bounds();
    let (minimum, maximum) = (minimum.to_string(), maximum.to_string());
    [
        relate(
            integer_literal(&minimum),
            to_integer(value),
            Relation::LessEqual,
        ),
        relate(
            to_integer(value),
            integer_literal(&maximum),
            Relation::LessEqual,
        ),
    ]
    .into_iter()
    .map(|bound| Carried {
        establish: Establish::Steps(vec![have(bound.clone(), vec![type_range(bound.clone())])]),
        surface: bound,
    })
    .collect()
}

/// What `solve`'s connected-equality chain may still spend.
struct RewriteBudget {
    attempts: usize,
    solve_closures: usize,
}

/// How the rewrite search closes each goal it reaches.
#[derive(Clone, Copy)]
pub(in crate::surface::proof) enum RewriteClosers<'p> {
    /// `known`, `normalize`, the direct logical closer, then a
    /// bounded nested `solve`: the context's facts.
    Ambient,
    /// The early goal-local route: direct/typed closure and optional
    /// function unfolding, without restarting all of `solve` before arithmetic.
    GoalLocal { allow_function_unfold: bool },
    /// The direct logical closer, `solve`'s typed atomic closer and
    /// `normalize`, for `solve`'s own premises: no nested `solve`, which
    /// would select the same premises and search them again.
    Selected,
    /// `normalize` and an atomic plan over these premises alone, for
    /// `solve() using`, which reads no ambient fact.
    Listed(&'p [(Proposition, ClickProposition)]),
}

/// Whether `kernel` is an equality the `rewrite` step can use.
fn is_rewrite_equality(kernel: &Proposition) -> bool {
    // Retained machine comparisons use exact Integer observations. They are
    // the same machine equalities this strategy already accepts, not a new
    // class of mathematical Integer rewrite candidates.
    if let Some((condition @ ConditionTerm::IntegerEqual(..), true)) = (kernel).condition_native()
        && let Some(view) =
            crate::kernel::machine_integer::comparison::structural_comparison_view(condition)
        && view.format.format().bits() <= 64
    {
        return true;
    }
    matches!(&kernel, condition_source @ Proposition::ConditionIs(_, true)
        if matches!(condition_source.condition_native(), Some((ConditionTerm::Compare {
            // An 8- or 16-bit equality rewrites at its own width.
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32 | MachineIntegerType::Int64
                | MachineIntegerType::Int8 | MachineIntegerType::UInt8 | MachineIntegerType::Int16 | MachineIntegerType::UInt16,
            relation: CompareRelation::Equal, ..
        } | ConditionTerm::AddressEqual(_, _) | ConditionTerm::PointerEqual(_, _) | ConditionTerm::AddressOffsetEqual(_, _), _))))
        || matches!(
            kernel,
            Proposition::Equal(Term::Algebraic(_), Term::Algebraic(_))
        )
}

/// An equality in both directions, each with its kernel form.
fn oriented_forms(
    kernel: Proposition,
    surface: ClickProposition,
) -> Vec<(Proposition, ClickProposition)> {
    // Arithmetic operands need an explicit observation when reparsed under
    // Integer arithmetic. Ordinary equalities retain their source spelling.
    let machine_arithmetic = crate::kernel::machine_integer::representation::is_ring_operation;
    let arithmetic = |mut operand: &ContractExpression| {
        loop {
            match operand {
                ContractExpression::Old(inner)
                | ContractExpression::At {
                    expression: inner, ..
                } => operand = inner,
                ContractExpression::Add(..)
                | ContractExpression::Subtract(..)
                | ContractExpression::Multiply(..)
                | ContractExpression::Negate(_) => return true,
                ContractExpression::ProgramExpression(
                    ProgramExpression::Add(..)
                    | ProgramExpression::Subtract(..)
                    | ProgramExpression::Multiply(..),
                ) => return true,
                ContractExpression::ProgramExpression(ProgramExpression::Value(value)) => {
                    return matches!(
                    value.numeric_value(), crate::kernel::integer_c_value!(term) if machine_arithmetic(term));
                }
                _ => return false,
            }
        }
    };
    let mut written = &surface;
    while let ClickProposition::At { proposition, .. } | ClickProposition::Not(proposition) =
        written
    {
        written = proposition;
    }
    let surface = if matches!(written,
        ClickProposition::Comparison { left, right, .. } if arithmetic(left) || arithmetic(right))
    {
        super::smart_closures::observed_native_surface_comparison(&kernel, &surface)
    } else {
        surface
    };
    let reverse = crate::kernel::proof::equality_rewrite::reverse_equality(&kernel).zip(
        super::fixed_state_proofs::reverse_surface_equality(&surface),
    );
    std::iter::once((kernel, surface)).chain(reverse).collect()
}

/// Preserve a native equality's carrier without turning it into an Integer
/// observation. This also makes arithmetic in a recorded source round-trip.
fn explicit_native_rewrite_equality(
    kernel: &Proposition,
    surface: &ClickProposition,
) -> Option<ClickProposition> {
    let Some((ConditionTerm::Compare { format, .. }, _)) = kernel.condition_native() else {
        return None;
    };
    fn cast(
        operand: &ContractExpression,
        format: crate::kernel::MachineIntegerType,
    ) -> ContractExpression {
        ContractExpression::CUnary {
            operand: Box::new(operand.clone()),
            lowered: ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Value(int32(0))),
                target_type: format.program_type(),
                integer_mode: crate::kernel::IntegerCastMode::CConversion,
                pointee_struct: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            },
        }
    }
    match surface {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => Some(ClickProposition::Comparison {
            left: cast(left, *format),
            operator: *operator,
            right: cast(right, *format),
        }),
        ClickProposition::At {
            selector,
            proposition,
        } => Some(ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(explicit_native_rewrite_equality(kernel, proposition)?),
        }),
        _ => None,
    }
}

/// `l == r` for an equality spelled `at(S, l) == at(S, r)` or `at(S, l == r)`.
fn unanchored_equality(surface: &ClickProposition) -> Option<ClickProposition> {
    match surface {
        ClickProposition::At { proposition, .. } => Some(proposition.as_ref().clone()),
        ClickProposition::Comparison {
            left:
                ContractExpression::At {
                    selector: left_selector,
                    expression: left,
                },
            operator,
            right:
                ContractExpression::At {
                    selector: right_selector,
                    expression: right,
                },
        } if left_selector == right_selector => Some(ClickProposition::Comparison {
            left: left.as_ref().clone(),
            operator: *operator,
            right: right.as_ref().clone(),
        }),
        _ => None,
    }
}

/// The two sides of an algebraic equality fact.
fn algebraic_sides(
    fact: &Proposition,
) -> Option<(&crate::kernel::AlgebraicTerm, &crate::kernel::AlgebraicTerm)> {
    match fact {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::AlgebraicEqual(left, right), _)) =
                condition_source_0.condition_native() =>
        {
            Some((left, right))
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => Some((left, right)),
        _ => None,
    }
}

fn is_constructor(term: &crate::kernel::AlgebraicTerm) -> bool {
    matches!(
        term.node,
        crate::kernel::AlgebraicTermNode::Constructor { .. }
    )
}

/// An `Integer` literal, negative ones as a negation of their magnitude.
fn integer_literal(text: &str) -> ContractExpression {
    match text.strip_prefix('-') {
        Some(magnitude) => ContractExpression::Negate(Box::new(
            ContractExpression::IntegerLiteral(magnitude.into()),
        )),
        None => ContractExpression::IntegerLiteral(text.into()),
    }
}

/// The sums and differences observed by `to_integer(...)` in `expression`.
fn observed_operations(expression: &ContractExpression, found: &mut Vec<ContractExpression>) {
    if let ContractExpression::Call { name, arguments } = expression
        && name == "to_integer"
        && let [argument] = arguments.as_slice()
        && matches!(
            argument,
            ContractExpression::Add(..) | ContractExpression::Subtract(..)
        )
        && !found.contains(argument)
    {
        found.push(argument.clone());
    }
    match expression {
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            observed_operations(left, found);
            observed_operations(right, found);
        }
        ContractExpression::Negate(value) => observed_operations(value, found),
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                observed_operations(argument, found);
            }
        }
        _ => {}
    }
}

fn proposition_operations(proposition: &ClickProposition) -> Vec<ContractExpression> {
    let mut found = Vec::new();
    if let ClickProposition::Comparison { left, right, .. } = proposition {
        observed_operations(left, &mut found);
        observed_operations(right, &mut found);
    }
    found
}

impl<'a> Proof<'a> {
    /// The specification functions in scope for this proof.
    fn spec_functions(&self) -> &'a ClickFunctionEnvironment {
        match self.context.as_ref() {
            ProofContext::Pure(context) => context.spec_definitions.functions,
            ProofContext::FixedState(context) => context.spec_definitions.functions,
            ProofContext::Execution(context) => context.spec_definitions.functions,
        }
    }
}

/// The proof `if`s `solve` writes through a definition, and their ends.
enum DefinitionPlan {
    Split {
        condition: ClickProposition,
        then_plan: Box<DefinitionPlan>,
        else_plan: Box<DefinitionPlan>,
    },
    /// An end, reached through `unfolds`: the applications of the ends
    /// followed into their definitions, each unfolded after the fact's own.
    End {
        unfolds: Vec<ClickFunctionApplication>,
        value: ContractExpression,
    },
}

/// What each end of a [`DefinitionPlan`] refutes: the fact `f(args) == k`,
/// by `f(args) != k` read from the definition with the goal false.
/// The goal a definition's conditions are compared with: as written, and
/// as lowered here.
struct DefinitionGoal<'g> {
    text: String,
    surface: &'g ClickProposition,
    kernel: &'g Proposition,
}

/// Whether two propositions are comparisons with the same operator, or
/// otherwise of the same kind: a lowered comparison is tried only then.
fn same_shape(left: &ClickProposition, right: &ClickProposition) -> bool {
    match (left, right) {
        (
            ClickProposition::Comparison { operator: left, .. },
            ClickProposition::Comparison {
                operator: right, ..
            },
        ) => left == right,
        _ => std::mem::discriminant(left) == std::mem::discriminant(right),
    }
}

struct DefinitionRefutation {
    application: ClickFunctionApplication,
    differs: ClickProposition,
    fact: ClickProposition,
}

/// An integer constant, or a `bool` one as `1` or `0`: a definition's end
/// and the value a fact gives its application.
fn definition_end_value(expression: &ContractExpression) -> Option<i128> {
    integer_literal_value(expression)
        .or_else(|| crate::surface::bool_literal_value(expression).map(i128::from))
}

fn integer_literal_value(expression: &ContractExpression) -> Option<i128> {
    match expression {
        ContractExpression::IntegerLiteral(text) => text.parse().ok(),
        _ => None,
    }
}

/// Whether either side of a written comparison is a sum or a difference.
fn writes_sum_or_difference(left: &ContractExpression, right: &ContractExpression) -> bool {
    [left, right].into_iter().any(|side| {
        matches!(
            side,
            ContractExpression::Add(..) | ContractExpression::Subtract(..)
        )
    })
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/proof/selected_arithmetic.rs");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retained_machine_rewrite_candidates_keep_the_native_scope() {
        use crate::kernel::{IntegerTerm, KernelTerm, KernelType, SharedMachineIntegerTerm};
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt8,
            MachineIntegerType::Int16,
            MachineIntegerType::UInt16,
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
            MachineIntegerType::UInt128,
        ] {
            let side = |id| {
                IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(
                        format,
                        KernelTerm::variable(
                            KernelType::Program(format.program_type()),
                            Variable(id),
                        ),
                    )
                    .unwrap(),
                )
                .into()
            };
            let equality = ConditionTerm::IntegerEqual(side(995450), side(995451));
            assert_eq!(
                is_rewrite_equality(&Proposition::condition_is(equality.clone(), true)),
                format.format().bits() <= 64
            );
            assert!(!is_rewrite_equality(&Proposition::condition_is(
                equality, false
            )));
            assert!(!is_rewrite_equality(&Proposition::condition_is(
                ConditionTerm::IntegerNotEqual(side(995450), side(995451)),
                true
            )));
        }
        assert!(!is_rewrite_equality(&Proposition::condition_is(
            ConditionTerm::IntegerEqual(
                IntegerTerm::Variable(Variable(995452)).into(),
                IntegerTerm::Variable(Variable(995453)).into()
            ),
            true
        )));
    }

    #[test]
    fn retained_shift_bounds_expand_and_replay_without_search() {
        for (premise, goal) in [
            ("(v >> 32) != 0u64", "4294967296u64 <= v"),
            ("(v >> 32) == 0u64", "v < 4294967296u64"),
            ("not ((v >> 32) != 0u64)", "v < 4294967296u64"),
        ] {
            let source = format!(
                r#"
theorem shift_bound(v: uint64) {{
    requires {premise};
    ensures {goal} by {{
        solve();
    }}
}}
"#
            );
            crate::surface::verify_click_theorems(&source).unwrap();
            let line = source
                .lines()
                .position(|line| line.contains("solve()"))
                .unwrap();
            let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
            let expanded =
                crate::surface::expand_c_tactic_source_at(&source, &[], line + 1, column + 1)
                    .unwrap();
            assert!(!expanded.contains("normalize("), "{expanded}");
            assert!(!expanded.contains("solve("), "{expanded}");
            assert!(!expanded.contains("operation_bound"), "{expanded}");
            without_implicit_solve(|| crate::surface::verify_click_theorems(&expanded)).unwrap();
            let missing = source.replace(&format!("    requires {premise};\n"), "");
            assert!(crate::surface::verify_click_theorems(&missing).is_err());
        }
    }

    #[test]
    fn listed_narrowed_length_equalities_expand_to_explicit_rewrites() {
        let source = r#"
import click::c::stdio;
theorem narrowed_length_result(n: uint64, result: int32) {
    requires stdio::padded_length(n, 3u64) == 3u64;
    requires result == (1u64 + stdio::padded_length(n, 3u64)) as int32;
    ensures result == 4 by {
        solve() using {
            result == (1u64 + stdio::padded_length(n, 3u64)) as int32;
            stdio::padded_length(n, 3u64) == 3u64;
        };
    }
}
"#;
        crate::surface::verify_click_theorems(source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
        let expanded =
            crate::surface::expand_c_tactic_source_at(source, &[], line + 1, column + 1).unwrap();
        assert!(expanded.contains("rewrite("), "{expanded}");
        without_implicit_solve(|| crate::surface::verify_click_theorems(&expanded)).unwrap();
        let missing = source
            .replace("    requires stdio::padded_length(n, 3u64) == 3u64;\n", "")
            .replace("            stdio::padded_length(n, 3u64) == 3u64;\n", "");
        assert!(crate::surface::verify_click_theorems(&missing).is_err());
    }

    fn check_listed_operation_identity(ty: &str, bound: &str, operation: &str) {
        let op = if operation.contains('+') { "+" } else { "-" };
        let source = format!(
            r#"
theorem identity(x: {ty}) {{
    requires {bound};
    ensures to_integer({operation}) == to_integer(x) {op} 1 by {{
        solve() using {{ {bound}; }};
    }}
}}
"#
        );
        crate::surface::verify_click_theorems(&source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
        let expanded =
            crate::surface::expand_c_tactic_source_at(&source, &[], line + 1, column + 1).unwrap();
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(expanded.contains("known();"), "{expanded}");
        without_implicit_solve(|| crate::surface::verify_click_theorems(&expanded)).unwrap();
        let omitted = source.replace(&format!("using {{ {bound}; }}"), "using {}");
        assert!(
            crate::surface::verify_click_theorems(&omitted).is_err(),
            "an unlisted no-wrap bound must not be read: {omitted}"
        );
    }

    #[test]
    fn listed_premises_prove_signed_add_identity() {
        check_listed_operation_identity("int32", "x < 2147483647", "x + 1");
    }

    #[test]
    fn listed_premises_prove_signed_subtract_identity() {
        check_listed_operation_identity("int32", "x > -2147483648", "x - 1");
    }

    #[test]
    fn listed_premises_prove_unsigned_add_identity() {
        check_listed_operation_identity("uint64", "x < 18446744073709551615u64", "x + 1u64");
    }

    #[test]
    fn listed_premises_prove_unsigned_subtract_identity() {
        check_listed_operation_identity("uint64", "x > 0u64", "x - 1u64");
    }

    /// `solve` plans a product's in-range identity at a format other than
    /// `int32`. At `uint16` the lower bound `0 <= to_integer(a) *
    /// to_integer(b)` is no fact; it comes from the operands' type ranges by
    /// an explicit product-lower-bound library application. The expansion
    /// retains the identity separately and replays with no search.
    #[test]
    fn solve_plans_a_product_identity_from_its_operand_ranges() {
        let source = r#"
theorem product_identity(a: uint16, b: uint16) {
    requires to_integer(a) * to_integer(b) <= 65535;
    let r: uint16 = a * b;
    ensures to_integer(r) == to_integer(a) * to_integer(b) by {
        have to_integer(r) == to_integer(a) * to_integer(b) by solve();
        known();
    }
}
"#;
        crate::surface::verify_click_theorems(source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("by solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
        let expanded =
            crate::surface::expand_c_tactic_source_at(source, &[], line + 1, column + 1).unwrap();
        assert!(expanded.contains("::product_lower_bound("), "{expanded}");
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(expanded.contains("known();"), "{expanded}");
        without_implicit_solve(|| crate::surface::verify_click_theorems(&expanded)).unwrap();
        // Without the upper bound the product may wrap; nothing gives it.
        let unbounded =
            source.replace("    requires to_integer(a) * to_integer(b) <= 65535;\n", "");
        assert!(crate::surface::verify_click_theorems(&unbounded).is_err());
    }

    /// `a <= b` and `a != b` give `a < b` by the Integer certificate's
    /// `less_than_from_not_equal` at `int64` and over `Integer`; before, only
    /// the `signed_int32` certificate had the step. The expansion replays
    /// with no search.
    #[test]
    fn solve_makes_a_bound_strict_by_a_disequality_at_every_format() {
        for ty in ["int64", "Integer"] {
            let source = format!(
                r#"
theorem strict(a: {ty}, b: {ty}) {{
    requires a <= b;
    requires a != b;
    ensures a < b by {{
        have a < b by solve();
        known();
    }}
}}
"#
            );
            crate::surface::verify_click_theorems(&source).unwrap();
            let line = source
                .lines()
                .position(|line| line.contains("by solve()"))
                .unwrap();
            let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
            let expanded =
                crate::surface::expand_c_tactic_source_at(&source, &[], line + 1, column + 1)
                    .unwrap();
            assert!(
                expanded.contains("click::integer::le_ne_lt"),
                "{ty}: {expanded}"
            );
            without_implicit_solve(|| crate::surface::verify_click_theorems(&expanded)).unwrap();
            let unequal = source.replace("    requires a != b;\n", "");
            assert!(
                crate::surface::verify_click_theorems(&unequal).is_err(),
                "{ty}: `a <= b` alone gives no strict bound"
            );
        }
    }

    #[test]
    fn solve_proves_an_equality_operation_identity_once() {
        // Each bound of the split equality is proved inside its own `have`,
        // which drops the identities proved there, so proving them per bound
        // would prove `to_integer(x + 1) == to_integer(x) + 1` twice.
        let source = r#"
theorem successor_identity(x: int32) {
    requires x < 2147483647;
    ensures to_integer(x + 1) == to_integer(x) + 1 by {
        have to_integer(x + 1) == to_integer(x) + 1 by solve();
        known();
    }
}
"#;
        crate::surface::verify_click_theorems(source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("by solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
        let expanded =
            crate::surface::expand_c_tactic_source_at(source, &[], line + 1, column + 1).unwrap();
        // The source's outer have and one generated identity proof.
        assert_eq!(
            expanded
                .matches("have to_integer((x + 1)) == (to_integer(x) + 1) by")
                .count(),
            2,
            "{expanded}"
        );
        crate::surface::verify_click_theorems(&expanded).unwrap();
    }

    /// `solve` reaches its simplification before splitting a plain 64-bit
    /// equality into its two bounds, each of which would run a nested search.
    #[test]
    fn selected_arithmetic_leaves_a_plain_64_bit_equality_to_general_solve() {
        let source = r#"spec enum Color { Red, Black, }
function color_bit(color: Color) -> int32 {
    match color { Color::Red => 0, Color::Black => 1, }
}
theorem low_bit_is_the_color_bit(bits: uint64, color: Color) {
    requires (bits & 1u64) == color_bit(color) as uint64;
    ensures (bits & 1u64) == color_bit(color) as uint64 by {
        have (bits & 1u64) == color_bit(color) as uint64 by solve();
        known();
    }
}
"#;
        crate::surface::verify_click_theorems(source).unwrap();
        let line = source
            .lines()
            .position(|line| line.contains("by solve()"))
            .unwrap();
        let column = source.lines().nth(line).unwrap().find("solve()").unwrap();
        let expanded =
            crate::surface::expand_c_tactic_source_at(source, &[], line + 1, column + 1).unwrap();
        assert!(!expanded.contains("equal_from_bounds"), "{expanded}");
        crate::surface::verify_click_theorems(&expanded).unwrap();
    }

    #[test]
    fn native_function_equalities_keep_contradiction_proofs_complete() {
        crate::surface::verify_click_theorems(
            r#"spec enum Color { Red, Black, }
function color_black(color: Color) -> int32 {
    match color { Color::Red => 0, Color::Black => 1, }
}
theorem black_color_is_black(color: Color) {
    requires color_black(color) == 1;
    ensures color == Color::Black by {
        let ih = induct(color);
        match color {
            Color::Red => {
                have not(color_black(Color::Red) == 1);
                contradiction(color_black(Color::Red) == 1);
            }
            Color::Black => { normalize(); }
        }
    }
}
"#,
        )
        .unwrap();
    }

    /// The connected-equality rewrite search is `solve`'s, so `solve()` alone
    /// proves what used to need `solve()`.
    #[test]
    fn solve_runs_the_connected_equality_rewrite_search() {
        crate::surface::verify_click_theorems(
            r#"spec enum Color { Red, Black, }
function color_black(color: Color) -> int32 {
    match color { Color::Red => 0, Color::Black => 1, }
}
theorem black_color_is_black(color: Color) {
    requires color_black(color) == 1;
    ensures color == Color::Black by {
        let ih = induct(color);
        match color {
            Color::Red => {
                have not(color_black(Color::Red) == 1) by solve();
                contradiction(color_black(Color::Red) == 1);
            }
            Color::Black => { normalize(); }
        }
    }
}
"#,
        )
        .unwrap();
    }

    #[test]
    fn native_rewrite_operands_survive_integer_source_expansion() {
        let used = MachineTerm::Variable(Variable(920_001));
        let capacity = MachineTerm::Variable(Variable(920_002));
        let slots = MachineTerm::Variable(Variable(920_003));
        let kernel = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(capacity),
                right: Box::new(binary_node!(Int32, Add, Box::new(used), Box::new(slots))),
            },
            true,
        );
        let name = |name: &str| {
            ContractExpression::ProgramExpression(ProgramExpression::Variable(name.into()))
        };
        let surface = ClickProposition::Comparison {
            left: name("capacity"),
            operator: ComparisonOperator::Equal,
            right: ContractExpression::Add(Box::new(name("used")), Box::new(name("slots"))),
        };
        let forms = oriented_forms(kernel, surface);
        assert_eq!(forms.len(), 2);
        let rewrite =
            crate::surface::printing::format_partial_tactic_sequence(&[ProofTactic::Rewrite(
                forms[0].1.clone(),
            )]);
        let source = format!(
            r#"
            theorem zero_remainder(used: int32, capacity: int32, slots: int32) {{
                requires defined(used + slots);
                requires defined(slots - capacity);
                requires to_integer(capacity) == to_integer(used) + to_integer(slots);
                requires used == 0;
                ensures to_integer(slots - capacity) == 0 by {{
                    have to_integer(slots - capacity) == 0 by {{
                        {rewrite}
                        rewrite(used, 0);
                        normalize();
                    }}
                    known();
                }}
            }}
        "#
        );
        crate::surface::verify_click_theorems(&source).unwrap();
    }
}

// Discovery methods are deliberately not methods of Proof.

// Source spelling adapters for the kernel ProofSearch interface.
mod search;

#[cfg(test)]
#[test]
#[ignore = "nightly: definition refutation expansion and strict replay"]
fn definition_refutation_expands_with_branch_equations() {
    use crate::surface::{
        expand_c_claim_source_by_label, verify_c_sources, without_implicit_solve,
    };
    for source in [
        r#"
        function choose(x: int32, y: int32) -> int32 {
            if x == 0 { if y == 0 { 1 } else { 2 } } else { 0 }
        }
        theorem forced(x: int32, y: int32) {
            requires choose(x, y) == 1;
            ensures y == 0;
        }
        "#,
        r#"
        import click::list;
        theorem forced(v: int32, x: int32) {
            requires list::contains(List<int32>::Cons(v, List<int32>::Nil), x);
            ensures v == x;
        }
        "#,
    ] {
        let expanded = expand_c_claim_source_by_label(source, &[], "forced.ensures_0")
            .unwrap_or_else(|error| panic!("{}\n{source}", error.message()));
        assert!(expanded.contains("unfold("), "{expanded}");
        assert!(expanded.contains("contradiction("), "{expanded}");
        assert!(!expanded.contains("normalize("), "{expanded}");
        assert!(!expanded.contains("solve("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &[]))
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }
}
