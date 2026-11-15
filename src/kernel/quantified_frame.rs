//! The checked quantified frame: one explicit transport of a proposition,
//! possibly quantified, whose memory reads name one state to the same
//! proposition reading another, decided leaf by leaf in the querying context
//! with each universal binder renamed fresh.
//!
//! It exists for quantified facts. A fact such as
//!
//! ```text
//! forall (k: int32) { 0 <= k and k < n implies at(before, left[k]) == left[k] }
//! ```
//!
//! is carried across `visited[cur] = 1` in one step instead of by `intro`,
//! `extract`, a per-index transport and `known`.
//!
//! **The rule.** `prove(from, to, context)` establishes `from => to`:
//!
//! - equal propositions hold;
//! - `forall (k: T)` on both sides, for a C integer `T` (`int32`, `int64`,
//!   or a machine integer such as `uint64`): both bodies are renamed to one binder
//!   identity no fact mentions ([`ProofFacts::freshen_int32_forall_body`], the
//!   identity `intro` chooses), so no fact about another `k` can decide a
//!   read of this one, and the bodies are proved for that arbitrary `k`;
//! - `from_a -> from_c` to `to_a -> to_c`: under `to_a`, prove
//!   `to_a => from_a` and `from_c => to_c` (an implication is antitone in its
//!   antecedent, so the antecedent is proved in the opposite direction);
//! - conjunctions and disjunctions componentwise; `not a => not b` as
//!   `b => a`;
//! - `a and b => c`, for a target `c` that is not a conjunction, from
//!   `a => c` or `b => c` (conjunction elimination: a guarded postcondition
//!   `defined(p[k]) and p[k] == v` carries its value conjunct alone);
//! - a condition leaf when its two spellings differ only in load atoms each
//!   shown unchanged between its two states (the kernel's checked load
//!   equality, `explicit_atomic_equality_from_memory_derivations` and the
//!   condition bridge's `memory_loads_proven_equal`), or when the caller's
//!   `leaf` check, the ordinary single-fact transport, carries it.
//! - a typed-read definedness leaf through the ordinary single-fact transport,
//!   which preserves initialization and lifetime evidence for that read.
//!
//! What this rule adds to a single `transport` is only *which facts a read
//! may use*: the read-history question reads the querying context's own
//! facts, as the fold read frame reads them, plus the guards over freshly
//! renamed binders, rather than only the facts a `using` list repeats. The
//! single-fact fallback reads what the single-fact route reads (its listed
//! and certified premises) plus the guards, so its cost is that route's.
//! Every per-read decision is the kernel's existing store, call and history
//! rule.
//!
//! **Why this is sound.** Each leaf is a checked implication in a context
//! that is the current proof context plus antecedents assumed on the proving
//! side, and each binder is fresh, so the leaf holds for an arbitrary value;
//! the connective cases are the monotonicity laws of the logic. The answer is
//! this query's derivation: it is recorded on no edge, never names a term,
//! and enters no assumption-free cache.

use super::assumptions::{conditions_equal_with_load_atoms, pointers_equal_with_load_atoms};
use super::primitives::*;
use super::proof::ProofFacts;
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use std::cell::Cell;
use std::collections::BTreeSet;

/// The single-fact transport a leaf may fall back to: does `from` carry to
/// `to` under these assumptions.
pub(crate) type FrameLeafCheck<'a> =
    &'a dyn Fn(&Proposition, &Proposition, &PureFactContext) -> bool;

/// What the caller's context adds once an antecedent is assumed: the facts
/// its resources expose under the extended assumptions (a guard can place a
/// read inside a range the context holds).
pub(crate) type FrameContextRefinement<'a> = &'a dyn Fn(PureFactContext) -> PureFactContext;

/// Why a quantified frame could not be established.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum QuantifiedFrameRefusal {
    /// The two propositions differ somewhere other than in condition leaves.
    ShapeMismatch,
    /// No leaf differs, so this rule has nothing to frame.
    NothingToFrame,
    /// No fresh binder identity was left.
    BinderExhausted,
    /// A condition leaf was not carried. The leaf's two sides are kept so a
    /// refusal can print both.
    LeafNotCarried {
        from: Box<Proposition>,
        to: Box<Proposition>,
    },
}

impl std::fmt::Display for QuantifiedFrameRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ShapeMismatch => {
                formatter.write_str(
                    "source and target differ outside their condition or definedness leaves",
                )
            }
            Self::NothingToFrame => {
                formatter.write_str("no condition or definedness leaf differs between source and target")
            }
            Self::BinderExhausted => {
                formatter.write_str("no fresh identity was left for a universal binder")
            }
            Self::LeafNotCarried { .. } => formatter.write_str(
                "a leaf was not carried: a read in it was not shown unchanged between its two states by the steps between them and this context's facts",
            ),
        }
    }
}

/// The quantified frame rule: `target` follows from `source` leaf by leaf.
/// See the module documentation for the rule and its soundness.
///
/// `assumptions` is the querying context the read-history question reads.
/// `leaf_assumptions` is the smaller context the single-fact transport
/// `leaf` reads for definedness or a condition not decided by its reads:
/// the transport's own listed and certified premises, as the single-fact
/// route reads them, so a fallback costs what that route costs. Each assumed
/// antecedent joins both. `facts` supplies the identities a fresh binder must
/// avoid, and `refine` adds what the context exposes once an antecedent is
/// assumed.
/// `context_variables` are the identities the context's facts beyond `facts`
/// mention; a renamed binder must avoid them too.
///
/// Work is linear in the two propositions plus one checked leaf question per
/// differing leaf.
pub(crate) fn frame_quantified_transport(
    source: &Proposition,
    target: &Proposition,
    facts: &ProofFacts,
    assumptions: &PureFactContext,
    leaf_assumptions: &PureFactContext,
    leaf: FrameLeafCheck<'_>,
    refine: FrameContextRefinement<'_>,
    context_variables: &BTreeSet<Variable>,
) -> Result<(), QuantifiedFrameRefusal> {
    let framer = Framer {
        facts,
        leaf,
        refine,
        context_variables,
        framed_leaves: Cell::new(0),
    };
    let contexts = Contexts {
        reads: assumptions.clone(),
        leaf: leaf_assumptions.clone(),
        fresh_binder: false,
    };
    framer.prove(source, target, &contexts)?;
    if framer.framed_leaves.get() == 0 {
        return Err(QuantifiedFrameRefusal::NothingToFrame);
    }
    Ok(())
}

/// The two contexts one position of the walk reads: the whole querying
/// context for read histories, and the single-fact route's own for leaves.
struct Contexts {
    reads: PureFactContext,
    leaf: PureFactContext,
    /// A universal binder was just renamed and its guard is not yet assumed:
    /// the next antecedent is the guard the context's resources may read.
    fresh_binder: bool,
}

struct Framer<'a> {
    facts: &'a ProofFacts,
    leaf: FrameLeafCheck<'a>,
    refine: FrameContextRefinement<'a>,
    context_variables: &'a BTreeSet<Variable>,
    framed_leaves: Cell<usize>,
}

impl Framer<'_> {
    /// Establishes `from => to` under `contexts`.
    fn prove(
        &self,
        from: &Proposition,
        to: &Proposition,
        contexts: &Contexts,
    ) -> Result<(), QuantifiedFrameRefusal> {
        crate::instrumentation::record_deterministic_work(1);
        match (from, to) {
            (left, right) if left == right => Ok(()),
            (
                Proposition::ForAll {
                    var: from_var,
                    sort: from_sort,
                    body: from_body,
                    ..
                },
                Proposition::ForAll {
                    var: to_var,
                    sort: to_sort,
                    body: to_body,
                    ..
                },
            ) if from_sort == to_sort
                && matches!(
                    from_sort,
                    Sort::ProgramInt32
                        | Sort::Bitvector32
                        | Sort::ProgramInt64
                        | Sort::ProgramInteger(_)
                ) =>
            {
                // One binder identity for both bodies. When the two lowerings
                // chose different identities, the second is renamed to the
                // first only where that cannot capture a free variable.
                let to_body = if from_var == to_var {
                    to_body.as_ref().clone()
                } else if crate::kernel::proposition_variables(to_body).contains(from_var) {
                    return Err(QuantifiedFrameRefusal::ShapeMismatch);
                } else {
                    crate::kernel::substitute_int32_variable_in_proposition(
                        to_body,
                        *to_var,
                        MachineTerm::Variable(*from_var),
                    )
                };
                let both = Proposition::And(from_body.clone(), Box::new(to_body));
                let (fresh, renamed) = self
                    .facts
                    .freshen_int32_forall_body(*from_var, &both)
                    .ok_or(QuantifiedFrameRefusal::BinderExhausted)?;
                // The identity is fresh for the proof's facts; the context
                // also holds effect and resource facts, and a guard on an
                // identity one of them mentions would constrain it too.
                if self.context_variables.contains(&fresh) {
                    return Err(QuantifiedFrameRefusal::BinderExhausted);
                }
                let Proposition::And(from_body, to_body) = renamed else {
                    return Err(QuantifiedFrameRefusal::ShapeMismatch);
                };
                let contexts = Contexts {
                    reads: contexts.reads.clone(),
                    leaf: contexts.leaf.clone(),
                    fresh_binder: true,
                };
                self.prove(&from_body, &to_body, &contexts)
            }
            (
                Proposition::Implies(from_antecedent, from_consequent),
                Proposition::Implies(to_antecedent, to_consequent),
            ) => {
                // The resources are asked again once per binder, for the
                // guard that bounds it, not once per nested implication.
                let reads = contexts
                    .reads
                    .clone()
                    .assume_proposition(to_antecedent.as_ref().clone());
                let guarded = Contexts {
                    reads: if contexts.fresh_binder {
                        (self.refine)(reads)
                    } else {
                        reads
                    },
                    leaf: contexts
                        .leaf
                        .clone()
                        .assume_proposition(to_antecedent.as_ref().clone()),
                    fresh_binder: false,
                };
                self.prove(to_antecedent, from_antecedent, &guarded)?;
                self.prove(from_consequent, to_consequent, &guarded)
            }
            (Proposition::And(a, b), Proposition::And(c, d))
            | (Proposition::Or(a, b), Proposition::Or(c, d)) => {
                self.prove(a, c, contexts)?;
                self.prove(b, d, contexts)
            }
            (Proposition::Not(a), Proposition::Not(b)) => self.prove(b, a, contexts),
            // Conjunction elimination, `a and b => c` from `a => c` or
            // `b => c`, when the target is not itself a conjunction (which
            // the componentwise case above takes). The walk descends only
            // the source's conjunction spine, once per target position.
            (Proposition::And(a, b), _) if !matches!(to, Proposition::And(_, _)) => {
                let framed = self.framed_leaves.get();
                let first = self.prove(a, to, contexts);
                if first.is_ok() {
                    return first;
                }
                // A failed first conjunct leaves no framed leaf behind.
                self.framed_leaves.set(framed);
                self.prove(b, to, contexts).map_err(|second| match second {
                    QuantifiedFrameRefusal::ShapeMismatch => first.unwrap_err(),
                    other => other,
                })
            }
            (
                Proposition::MemoryReadDefined {
                    value_type: from_type,
                    ..
                },
                Proposition::MemoryReadDefined {
                    value_type: to_type,
                    ..
                },
            ) if from_type == to_type => {
                // Definedness needs typed-read evidence; equal read values
                // alone do not establish initialization or preserve lifetime.
                if (self.leaf)(from, to, &contexts.leaf) {
                    self.framed_leaves.set(self.framed_leaves.get() + 1);
                    Ok(())
                } else {
                    Err(QuantifiedFrameRefusal::LeafNotCarried {
                        from: Box::new(from.clone()),
                        to: Box::new(to.clone()),
                    })
                }
            }
            (
                Proposition::ConditionIs(left, left_value),
                Proposition::ConditionIs(right, right_value),
            ) if left_value == right_value => {
                let carried = conditions_equal_with_load_atoms(left, right, &|left, right| {
                    loads_unchanged(left, right, &contexts.reads)
                }) || (self.leaf)(from, to, &contexts.leaf);
                if carried {
                    self.framed_leaves.set(self.framed_leaves.get() + 1);
                    Ok(())
                } else {
                    Err(QuantifiedFrameRefusal::LeafNotCarried {
                        from: Box::new(from.clone()),
                        to: Box::new(to.clone()),
                    })
                }
            }
            _ => Err(QuantifiedFrameRefusal::ShapeMismatch),
        }
    }
}

/// One pair of load atoms: one address (its own loads compared in turn) read
/// at two states, shown to hold one version by the kernel's checked load
/// equality, exactly as the condition bridge
/// (`conditions_equal_modulo_origin_unchanged`) asks it.
fn loads_unchanged(left: &MachineTerm, right: &MachineTerm, assumptions: &PureFactContext) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    if left == right {
        return true;
    }
    let (
        MachineTerm::MemoryLoad(_, left_pointer, left_kind),
        MachineTerm::MemoryLoad(right_memory, right_pointer, right_kind),
    ) = (left, right)
    else {
        return false;
    };
    // Reads of one address are one value only when they are one kind.
    if left_kind != right_kind {
        return false;
    }
    // Two spellings of one address: with its inner reads shown unchanged,
    // the right side's load at the left side's address has the right side's
    // value.
    if left_pointer != right_pointer
        && !pointers_equal_with_load_atoms(left_pointer, right_pointer, &|a, b| {
            loads_unchanged(a, b, assumptions)
        })
    {
        return false;
    }
    let right_at_left_address =
        MachineTerm::MemoryLoad(right_memory.clone(), left_pointer.clone(), *right_kind);
    crate::kernel::memory_provenance::explicit_atomic_equality_from_memory_derivations(
        left,
        &right_at_left_address,
        assumptions,
    ) || assumptions.memory_loads_proven_equal(left, &right_at_left_address)
}

#[cfg(test)]
mod wide_condition_tests {
    use super::*;

    // Adding a wide condition constructor must retain the load checker's exact
    // width/history requirements and must not identify different scalar values.
    #[test]
    fn wide_equality_frame_checks_read_kind_history_and_other_operand() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "wide-equality-frame".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let assumptions = PureFactContext::new();
        let before = Memory::new().with_block("wide-equality-frame", 16);
        let after = before.clone().store(
            pointer.offset_by_bytes(8),
            ProgramValue::UInt64(MachineTerm::uint64_constant(3)),
        );
        let load = |memory: &Memory, kind| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(memory),
                Box::new(pointer.clone()),
                kind,
            )
        };
        let condition = |read, value| ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: Box::new(read),
            right: Box::new(value),
        };
        let stamp = MachineTerm::uint64_constant(0x1_0000_0001);
        let source = condition(load(&before, LoadKind::Bits64), stamp.clone());
        let target = condition(load(&after, LoadKind::Bits64), stamp.clone());
        let carried = |target: &ConditionTerm| {
            conditions_equal_with_load_atoms(&source, target, &|left, right| {
                loads_unchanged(left, right, &assumptions)
            })
        };
        assert!(carried(&target));
        assert!(!carried(&condition(
            load(&after, LoadKind::Int32),
            stamp.clone()
        )));
        assert!(!carried(&condition(
            load(&after, LoadKind::Bits64),
            MachineTerm::uint64_constant(1),
        )));
        let partial = before.clone().store(
            pointer.offset_by_bytes(4),
            ProgramValue::Int32(MachineTerm::constant(0)),
        );
        assert!(!carried(&condition(
            load(&partial, LoadKind::Bits64),
            stamp
        )));
        assert!(!conditions_equal_with_load_atoms(
            &source,
            &ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(load(&after, LoadKind::Bits64)),
                right: Box::new(MachineTerm::constant(1))
            },
            &|_, _| true,
        ));
    }
}

#[cfg(test)]
mod conjunct_elimination_tests {
    use super::*;

    #[cfg(test)]
    mod scaling_tests {
        include!("../scaling_tests/kernel/quantified_frame/conjunct_elimination_tests.rs");
    }

    // Conjunction elimination drops a conjunct only when the remaining one is
    // itself carried, and dropping a conjunct alone frames nothing.
    #[test]
    fn a_conjunct_is_eliminated_only_when_the_other_is_carried() {
        let _session = crate::kernel::VerificationSession::enter();
        let leaf =
            |name: u64| Proposition::ConditionIs(ConditionTerm::Variable(Variable(name)), true);
        // The stand-in single-fact route carries leaf 1 to leaf 2 and nothing else.
        let carries = |from: &Proposition, to: &Proposition, _: &PureFactContext| {
            *from == leaf(1) && *to == leaf(2)
        };
        let facts = ProofFacts::default();
        let assumptions = PureFactContext::new();
        let same = |context: PureFactContext| context;
        let variables = BTreeSet::new();
        let frame = |source: &Proposition, target: &Proposition| {
            frame_quantified_transport(
                source,
                target,
                &facts,
                &assumptions,
                &assumptions,
                &carries,
                &same,
                &variables,
            )
        };
        let both = |a, b| Proposition::And(Box::new(leaf(a)), Box::new(leaf(b)));
        assert_eq!(frame(&both(1, 3), &leaf(2)), Ok(()));
        assert_eq!(frame(&both(3, 1), &leaf(2)), Ok(()));
        assert!(matches!(
            frame(&both(3, 4), &leaf(2)),
            Err(QuantifiedFrameRefusal::LeafNotCarried { .. })
        ));
        assert_eq!(
            frame(&both(1, 3), &leaf(3)),
            Err(QuantifiedFrameRefusal::NothingToFrame)
        );
    }
}
