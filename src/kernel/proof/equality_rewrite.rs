//! Checked equality substitution. Surface syntax is never evidence for a rewrite.

mod shared;
pub(in crate::kernel) use shared::canonical_index as canonical_pointer_index;

fn rewrite_pointer_index(
    value: &SharedMachineIntegerTerm,
    from: &MachineTerm,
    to: &MachineTerm,
) -> SharedMachineIntegerTerm {
    if let Some(root) = value.shared_operand() {
        shared::rewrite(root, from, to, |leaf| rewrite_term(leaf, from, to))
            .and_then(|root| SharedMachineIntegerTerm::from_shared(value.ty(), root))
            .unwrap_or_else(|| value.clone())
    } else {
        SharedMachineIntegerTerm::index(
            value.ty(),
            rewrite_term(
                value.retained_written_operand().expect("native index"),
                from,
                to,
            ),
        )
    }
}

pub(in crate::kernel) use shared::clear as clear_shared_exact_rewrite_cache;
pub(in crate::kernel) use shared::normalize_node as rebuild_normalized_machine_node;
pub(in crate::kernel) use shared::transport_node as rebuild_transported_machine_node;

use super::fact_reasoning::exactly_available_fact;
use super::{ProofFacts, PropositionObligation};
use crate::kernel::CompareRelation;
use crate::kernel::MachineTerm;
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::*;
use crate::kernel::{bits32_constant, constant_u32, int64_constant, uint64_constant};
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};

/// A checked goal refinement and its path-local load-transport evidence.
/// Only this module can construct or change its semantic result.
pub(crate) struct CheckedEqualityRewrite {
    proposition: Proposition,
    facts: ProofFacts,
}

impl CheckedEqualityRewrite {
    pub(crate) fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// A proposed surface spelling may use different load names. Accept it
    /// only through the kernel's checked, corresponding-leaf transport rule.
    pub(crate) fn try_present_as(&mut self, proposed: &Proposition) -> bool {
        if proposed == &self.proposition {
            return true;
        }
        // Surface lowering folds constant Integer expressions while an
        // exact substitution can leave their arithmetic structure intact.
        // Accept only the same normalized claim used by the checked Integer
        // certificate rules; this compares the selected propositions alone
        // and neither imports ambient facts nor transports different reads.
        if let (Some(original), Some(candidate)) = (
            super::integer_arithmetic::integer_affine_claim(&self.proposition),
            super::integer_arithmetic::integer_affine_claim(proposed),
        ) && original == candidate
        {
            self.proposition = proposed.clone();
            return true;
        }
        let Some(facts) = self
            .facts
            .with_checked_rewritten_loads(&self.proposition, proposed)
        else {
            return false;
        };
        self.facts = facts;
        self.proposition = proposed.clone();
        true
    }

    pub(crate) fn into_obligation<P, O>(
        self,
        presentation: P,
        outcome: Option<O>,
    ) -> (PropositionObligation<P, O>, ProofFacts) {
        let obligation = match outcome {
            Some(outcome) => {
                PropositionObligation::at_outcome(self.proposition, presentation, outcome)
            }
            None => PropositionObligation::new(self.proposition, presentation),
        };
        (obligation, self.facts)
    }
}

impl ProofFacts {
    /// Check one explicitly cited equality against the persistent premise
    /// index, then compute the exact substitution. This path never scans or
    /// rebuilds the ambient premise context. Goal lowering/unfolding precedes
    /// this rule; the returned obligation contains only the checked result.
    pub(crate) fn check_equality_rewrite(
        &self,
        goal: &Proposition,
        equality: &Proposition,
    ) -> Result<CheckedEqualityRewrite, String> {
        let admitted = equality_is_vacuous(equality)
            || self.materialization_available(equality)
            || reverse_equality(equality)
                .is_some_and(|reverse| self.materialization_available(&reverse));
        if !admitted {
            return Err(
                "`rewrite` requires its equality to be an exact available fact".to_string(),
            );
        }
        match rewrite_with_admitted_equality(goal, equality) {
            Ok(proposition) => Ok(CheckedEqualityRewrite {
                proposition,
                facts: self.clone(),
            }),
            Err(original_error) => {
                // Compare only the cited expression with the two operands of
                // this atomic goal. Corresponding operators stay exact; the
                // shared transport checker validates any changed read leaves.
                let (from, to, wide) = match equality {
                    Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::Equal,
                            left: a,
                            right: b,
                        },
                        true,
                    ) => (a, b, false),
                    Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left: a,
                            right: b,
                        },
                        true,
                    ) => (a, b, true),
                    _ => return Err(original_error),
                };
                let (left, right) = match goal {
                    Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                            relation: CompareRelation::Equal,
                            left: a,
                            right: b,
                        },
                        _,
                    ) if !wide => (a, b),
                    Proposition::ConditionIs(
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left: a,
                            right: b,
                        },
                        _,
                    ) if wide => (a, b),
                    _ => return Err(original_error),
                };
                for selected in [left, right] {
                    if selected == from {
                        continue;
                    }
                    let condition = if wide {
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left: selected.clone(),
                            right: to.clone(),
                        }
                    } else {
                        ConditionTerm::equal(selected.as_ref().clone(), to.as_ref().clone())
                    };
                    let adapted = Proposition::ConditionIs(condition, true);
                    let Some(facts) = self.with_checked_rewritten_loads(equality, &adapted) else {
                        continue;
                    };
                    if let Ok(proposition) = rewrite_with_admitted_equality(goal, &adapted) {
                        return Ok(CheckedEqualityRewrite { proposition, facts });
                    }
                }
                Err(original_error)
            }
        }
    }
}

pub(crate) fn reverse_equality(equality: &Proposition) -> Option<Proposition> {
    if let Proposition::ConditionIs(ConditionTerm::BoolEqual(a, b), true) = equality {
        return Some(Proposition::ConditionIs(
            ConditionTerm::BoolEqual(b.clone(), a.clone()),
            true,
        ));
    }
    let reversed = match equality {
        Proposition::Equal(Term::Algebraic(a), Term::Algebraic(b)) => {
            return Some(Proposition::Equal(
                Term::Algebraic(b.clone()),
                Term::Algebraic(a.clone()),
            ));
        }
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            },
            true,
        ) => ConditionTerm::Compare {
            format: *format,
            relation: CompareRelation::Equal,
            left: b.clone(),
            right: a.clone(),
        },
        // A native 8- or 16-bit equality reverses at its own format.
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format:
                    format @ (MachineIntegerType::Int8
                    | MachineIntegerType::UInt8
                    | MachineIntegerType::Int16
                    | MachineIntegerType::UInt16),
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            },
            true,
        ) => ConditionTerm::Compare {
            format: *format,
            relation: CompareRelation::Equal,
            left: b.clone(),
            right: a.clone(),
        },
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: a,
                right: b,
            },
            true,
        ) => ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: b.clone(),
            right: a.clone(),
        },
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) => {
            ConditionTerm::IntegerEqual(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(a, b), true) => {
            ConditionTerm::PointerOffsetEqual(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::PointerValueEqual(a, b), true) => {
            ConditionTerm::PointerValueEqual(b.clone(), a.clone())
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(a, b), true) => {
            ConditionTerm::PointerEqual(b.clone(), a.clone())
        }
        _ => return None,
    };
    Some(Proposition::ConditionIs(reversed, true))
}

// Equality substitution cares about lexical variables, not the contents of
// immutable states. The shared checked collector also sees variables in
// pure-function arguments and registered load addresses.
fn rewrite_equality_variables(equality: &Proposition) -> Result<BTreeSet<Variable>, String> {
    let mut collector =
        crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::checked();
    collector.collect(equality);
    if collector.exhausted() {
        return Err(
            "`rewrite` exhausted its work budget while checking binder capture".to_string(),
        );
    }
    let mut variables = BTreeSet::new();
    collector.extend_into(&mut variables);
    Ok(variables)
}

/// Candidate construction for smart planning over an explicit premise slice.
/// The result has no proof authority; certificate checking uses the indexed
/// `ProofFacts::check_equality_rewrite` rule instead.
pub(crate) fn rewrite_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
    available: &[Proposition],
) -> Result<Proposition, String> {
    // Planning uses only the selected premises, in either orientation.
    // Discovering another equality through load chains or memory history is
    // a separate proof step, not part of applying this selected rewrite.
    let is_available = |fact: &Proposition| {
        available.contains(fact) || exactly_available_fact(fact, available).is_some()
    };
    if !equality_is_vacuous(equality)
        && !is_available(equality)
        && !reverse_equality(equality)
            .as_ref()
            .is_some_and(is_available)
    {
        return Err("`rewrite` requires its equality to be an exact available fact".to_string());
    }
    rewrite_with_admitted_equality(goal, equality)
}

/// Whether `equality` replaces some occurrence in `goal`. Smart planning
/// uses it to skip a rewrite that cannot apply; it has no proof authority,
/// and the checked `rewrite` step decides.
pub(crate) fn equality_rewrite_applies(goal: &Proposition, equality: &Proposition) -> bool {
    !equality_is_vacuous(equality)
        && rewrite_with_admitted_equality(goal, equality).is_ok_and(|rewritten| rewritten != *goal)
}

/// Rewrite `goal` by an admitted equality. A native comparison goal is the
/// Integer comparison of its exact observations, so an Integer equality such
/// as `to_integer(a + b) == to_integer(a) + to_integer(b)` may rewrite that
/// reading when it names nothing in the goal as written. Only the goal's own
/// constant number of readings are tried.
fn rewrite_with_admitted_equality(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, String> {
    let exact = rewrite_with_admitted_equality_as_written(goal, equality);
    if exact.is_ok() {
        return exact;
    }
    // Equality of mathematical integers implies equality of their residues.
    // This direction needs no in-range premise (unlike an order comparison).
    // Only the cited expression is visited, under the modular rule's bound.
    if let Proposition::ConditionIs(condition, truth) = equality {
        for width in [MachineIntegerType::UInt32, MachineIntegerType::UInt64] {
            if let Some(wrapped) = crate::kernel::machine_integer::modular::wrapped_equality_at(
                width, condition, *truth,
            ) && let Ok(rewritten) = rewrite_with_admitted_equality_reading(
                goal,
                &Proposition::ConditionIs(wrapped, true),
                true,
            ) {
                return Ok(rewritten);
            }
        }
    }
    for reading in
        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(goal)
    {
        if let Ok(rewritten) = rewrite_with_admitted_equality_as_written(&reading, equality) {
            return Ok(rewritten);
        }
    }
    exact
}

fn rewrite_with_admitted_equality_as_written(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, String> {
    rewrite_with_admitted_equality_reading(goal, equality, false)
}

// A projected residue equality substitutes words inside machine expressions,
// even when its comparison is stored as exact Integer observations.
fn rewrite_with_admitted_equality_reading(
    goal: &Proposition,
    equality: &Proposition,
    machine_equality: bool,
) -> Result<Proposition, String> {
    if equality_is_vacuous(equality) {
        return Ok(goal.clone());
    }
    let byte_equality = signed_byte_equality_as_byte_equality(equality);
    let equality = byte_equality.as_ref().unwrap_or(equality);
    enum RewriteTask<'a> {
        Visit(&'a Proposition),
        BuildAnd,
        BuildOr,
        BuildNot,
        BuildImplies,
        BuildForAll {
            var: Variable,
            sort: Sort,
            name: BinderName,
        },
        BuildExists {
            name: String,
            var: Variable,
            sort: Sort,
        },
    }

    let integer_source = match equality {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(from, _), true)
            if matches!(
                from.as_ref(),
                IntegerTerm::Machine(_) | IntegerTerm::Constant(_)
            ) =>
        {
            Some(from)
        }
        _ => None,
    };
    let mut tasks = vec![RewriteTask::Visit(goal)];
    let mut results: Vec<(Proposition, bool)> = Vec::new();
    let equality_variables = std::cell::OnceCell::new();
    let mut blocked_by_binder = false;
    while let Some(task) = tasks.pop() {
        crate::instrumentation::record_deterministic_work(1);
        match task {
            RewriteTask::Visit(proposition) => match proposition {
                Proposition::And(left, right) => {
                    tasks.push(RewriteTask::BuildAnd);
                    tasks.push(RewriteTask::Visit(right));
                    tasks.push(RewriteTask::Visit(left));
                }
                Proposition::Or(left, right) => {
                    tasks.push(RewriteTask::BuildOr);
                    tasks.push(RewriteTask::Visit(right));
                    tasks.push(RewriteTask::Visit(left));
                }
                Proposition::Not(body) => {
                    tasks.push(RewriteTask::BuildNot);
                    tasks.push(RewriteTask::Visit(body));
                }
                Proposition::Implies(antecedent, consequent) => {
                    tasks.push(RewriteTask::BuildImplies);
                    tasks.push(RewriteTask::Visit(consequent));
                    tasks.push(RewriteTask::Visit(antecedent));
                }
                Proposition::ForAll {
                    var,
                    sort,
                    body,
                    name,
                } => {
                    if equality_variables
                        .get_or_init(|| rewrite_equality_variables(equality))
                        .as_ref()
                        .map_err(Clone::clone)?
                        .contains(var)
                    {
                        // Substitution below this binder could replace a bound
                        // occurrence or capture a variable in the replacement.
                        blocked_by_binder = true;
                        results.push((proposition.clone(), false));
                    } else {
                        tasks.push(RewriteTask::BuildForAll {
                            var: *var,
                            sort: sort.clone(),
                            name: name.clone(),
                        });
                        tasks.push(RewriteTask::Visit(body));
                    }
                }
                Proposition::Exists {
                    name,
                    var,
                    sort,
                    body,
                } => {
                    if equality_variables
                        .get_or_init(|| rewrite_equality_variables(equality))
                        .as_ref()
                        .map_err(Clone::clone)?
                        .contains(var)
                    {
                        blocked_by_binder = true;
                        results.push((proposition.clone(), false));
                    } else {
                        tasks.push(RewriteTask::BuildExists {
                            name: name.clone(),
                            var: *var,
                            sort: sort.clone(),
                        });
                        tasks.push(RewriteTask::Visit(body));
                    }
                }
                atomic => {
                    // Select the equivalent Integer reading at each leaf,
                    // including when another leaf already rewrote directly.
                    // The source's complete interned observation identity
                    // selects its carrier and proves a root occurrence.
                    let reading = integer_source.filter(|_| !machine_equality).and_then(|source| {
                        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
                            atomic,
                        )
                        .into_iter()
                        .find(|reading| {
                            matches!(
                                reading,
                                Proposition::ConditionIs(
                                    crate::kernel::integer_comparison_condition!(left, right),
                                    _,
                                ) if left == source || right == source
                            )
                        })
                    });
                    let selected = reading.as_ref().unwrap_or(atomic);
                    let rewritten = if machine_equality {
                        rewrite_atomic_by_word_equality(selected, equality)
                    } else {
                        rewrite_atomic_proposition_by_exact_equality(selected, equality)
                    };
                    match rewritten {
                        // A rewritten comparison is rebuilt by its smart
                        // constructor, so it has the canonical form lowering
                        // gives the same source: `0 == 0` is `true`.
                        Ok(Proposition::ConditionIs(condition, value)) => results.push((
                            Proposition::ConditionIs(
                                super::term_rewrite::folded_machine_condition(condition),
                                value,
                            ),
                            true,
                        )),
                        Ok(rewritten) => results.push((rewritten, true)),
                        Err(AtomicRewriteRefusal::Absent(_)) => {
                            results.push((atomic.clone(), false));
                        }
                        Err(refusal) => return Err(refusal.into()),
                    }
                }
            },
            RewriteTask::BuildAnd | RewriteTask::BuildOr | RewriteTask::BuildImplies => {
                let (right, right_changed) = results.pop().expect("right rewrite result");
                let (left, left_changed) = results.pop().expect("left rewrite result");
                let rewritten = match task {
                    RewriteTask::BuildAnd => Proposition::And(Box::new(left), Box::new(right)),
                    RewriteTask::BuildOr => Proposition::Or(Box::new(left), Box::new(right)),
                    RewriteTask::BuildImplies => {
                        Proposition::Implies(Box::new(left), Box::new(right))
                    }
                    _ => unreachable!(),
                };
                results.push((rewritten, left_changed || right_changed));
            }
            RewriteTask::BuildNot => {
                let (body, changed) = results.pop().expect("negation rewrite result");
                results.push((Proposition::Not(Box::new(body)), changed));
            }
            RewriteTask::BuildForAll { var, sort, name } => {
                let (body, changed) = results.pop().expect("universal rewrite result");
                results.push((
                    Proposition::ForAll {
                        var,
                        sort,
                        name,
                        body: Box::new(body),
                    },
                    changed,
                ));
            }
            RewriteTask::BuildExists { name, var, sort } => {
                let (body, changed) = results.pop().expect("existential rewrite result");
                results.push((
                    Proposition::Exists {
                        name,
                        var,
                        sort,
                        body: Box::new(body),
                    },
                    changed,
                ));
            }
        }
    }
    let (rewritten, changed) = results.pop().expect("root rewrite result");
    debug_assert!(results.is_empty());
    changed
        .then_some(rewritten)
        .ok_or_else(|| {
            if blocked_by_binder {
                "`rewrite` cannot substitute an equality through a quantifier that binds one of its variables".to_string()
            } else {
                "`rewrite` equality does not occur in the current goal".to_string()
            }
        })
}

/// One byte, one name: an admitted `int8(u) == k`, with `u` a byte load and
/// `k` in `-128..=127`, rewrites as `u == k mod 256`.
///
/// A signed byte read is `MachineTerm::signed_byte(u)`, the conversion
/// of the byte's single (unsigned) name `u`, so every occurrence of the
/// signed read contains `u`. Substituting `u` therefore rewrites both the
/// signed reads (`int8(k mod 256)` folds back to `k`) and the unsigned reads
/// the original equality could not reach. Soundness: a `UInt8` load holds one
/// zero-extended byte, `0..=255`, and the conversion maps that range
/// bijectively onto `-128..=127`, so `int8(u) == k` holds exactly when
/// `u == k mod 256`. A constant outside `-128..=127` is the conversion of no
/// byte; that equality is kept as written and never becomes a satisfiable
/// byte equality. The reverse orientation `k == int8(u)`, which replaces a
/// constant, is also kept as written. The check is the equality's own two
/// operands; nothing else is consulted.
fn signed_byte_equality_as_byte_equality(equality: &Proposition) -> Option<Proposition> {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: from,
            right: to,
        },
        true,
    ) = equality
    else {
        return None;
    };
    let byte = from.signed_byte_operand()?;
    if !matches!(
        crate::kernel::eval::viewed_as_memory_load(byte),
        Some(MachineTerm::MemoryLoad(_, _, LoadKind::UInt8))
    ) {
        return None;
    }
    let signed = i8::try_from(to.as_const()? as i32).ok()?;
    Some(Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(byte.clone()),
            right: Box::new(MachineTerm::constant(u32::from(signed as u8))),
        },
        true,
    ))
}

/// Whether rewriting by this equality cannot change any goal: it states
/// that a term equals itself (a 32-bit word up to one σ, rule K6), or it has
/// already simplified to `true`.
///
/// Both arise when the prover resolves two forms a proof script still
/// distinguishes. The step is then vacuous rather than wrong, so it must not
/// be reported as a missing occurrence or an unsupported equality shape.
fn equality_is_vacuous(equality: &Proposition) -> bool {
    if matches!(
        equality,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    ) {
        return true;
    }
    match equality {
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => left == right,
        // σ(x) == x is x == x under rule K6: the same bits.
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        ) => left == right || left.is_sign_cast32_of(right),
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left,
                right,
            },
            true,
        ) => left == right,
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) => {
            if left == right {
                return true;
            }
            let (IntegerTerm::Machine(left), IntegerTerm::Machine(right)) =
                (left.as_ref(), right.as_ref())
            else {
                return false;
            };
            // This is a word equality only when both exact observations use
            // the same format. Signed and unsigned Integer values differ.
            let format = left.ty();
            if format != right.ty() || format.format().bits() != 32 {
                return false;
            }
            let (left, right) = (left.operand_view(), right.operand_view());
            let sign_cast_of = |left: MachineOperandView<'_>, right: MachineOperandView<'_>| {
                left.cast()
                    .is_some_and(|(encoding, source, destination, child)| {
                        encoding == MachineCastSpelling::Generic
                            && is_sign_cast32(source, destination)
                            && child.retain(format) == right.retain(format)
                    })
            };
            sign_cast_of(left, right) || sign_cast_of(right, left)
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            left == right
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => left == right,
        _ => false,
    }
}

/// `rewrite` looks through a load variable: the rewritten term may occur
/// inside the address of the load the variable stands for. Rewriting that
/// address and taking the canonical form of the rewritten load gives the
/// load variable (or recorded value) for the rewritten read — equality
/// substitution is congruent through a load whether the load is written as a
/// term or named by its variable. Deterministic: the registry view and the
/// canonical form are the same on check.
fn rewrite_through_load_variable(
    term: &MachineTerm,
    rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
) -> Option<MachineTerm> {
    let MachineTerm::Variable(variable) = term else {
        return None;
    };
    if !crate::kernel::is_load_variable(variable) {
        return None;
    }
    // Rewrite the address at the state where this load was observed.
    // Its canonical state may be a projected placeholder: it preserves
    // the original cell's value, but need not preserve a different address
    // exposed by the equality. The current epoch's origin retains that
    // execution history, just as it does for checked load transport.
    // Without a live origin, keep the variable's defining state.
    let (memory, pointer) = crate::kernel::registered_load_origin_for_variable(variable)
        .or_else(|| crate::kernel::registered_load_for_variable(variable))?;
    let kind = crate::kernel::registered_load_kind_for_variable(variable)?;
    let rewritten = rewrite_pointer(&pointer);
    if rewritten == pointer {
        return None;
    }
    // Address substitution preserves this observation's byte dependency.
    // Without recording it at the new address, naming an otherwise unseen
    // int32 read defaults to the eight-byte legacy pointer footprint. That
    // makes rewrite/replay depend on which reads smart search tried first.
    let bytes = crate::kernel::registered_load_bytes_for_variable(variable)?;
    crate::kernel::eval::record_load_access_width(memory.memory(), &rewritten, bytes);
    // The read at the rewritten address is named as lowering names it: by
    // its version, never by a value its cell holds, so the rewritten goal
    // is the one writing the new address gives (`a[j]` to `a[i]`, not to
    // what `a[i]` stores).
    Some(crate::kernel::canonical_form_of_load(
        memory, rewritten, kind,
    ))
}

/// Read definitions selected by one address substitution. Cache by read
/// identity, not by a deep memory or address key; misses are shared too.
type PointerReadRewrites = RefCell<HashMap<PointerBlock, Option<Pointer>>>;

/// Substitute through the selected read-definition chain, then rebuild it
/// outward. The explicit stack is bounded by those definitions, not a depth
/// cutoff. A repeated identity refuses a cyclic definition without looping.
fn rewrite_through_loaded_pointer_block(
    pointer: &Pointer,
    rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
    cache: &PointerReadRewrites,
) -> Option<Pointer> {
    fn name_read(
        memory: SharedMemory,
        address: Pointer,
        kind: Option<LoadKind>,
    ) -> Option<Pointer> {
        crate::instrumentation::record_deterministic_work(1);
        let Some(kind) = kind else {
            return Some(Pointer::version_read(&memory, &address));
        };
        // Name the legacy scalar-carrier read, too: folding stored bits can
        // discard the rewritten read or cease to be a pointer carrier.
        let load = crate::kernel::canonical_form_of_load(memory, address, kind);
        let variable = match load {
            MachineTerm::Variable(variable) => variable,
            load @ MachineTerm::MemoryLoad(_, _, _) => {
                crate::kernel::load_variable_for_term(&load)?.0
            }
            _ => return None,
        };
        Some(Pointer::symbolic(variable))
    }

    let mut cursor = pointer.clone();
    let mut seen = HashSet::new();
    let mut frames = Vec::new();
    let mut result = loop {
        crate::instrumentation::record_deterministic_work(1);
        let cached = cache.borrow().get(&cursor.block).cloned();
        if let Some(cached) = cached {
            break cached;
        }
        if !seen.insert(cursor.block.clone()) {
            break None;
        }
        let definition = match &cursor.block {
            PointerBlock::LoadedPointer(identity) => {
                crate::kernel::eval::registered_pointer_load(*identity)
                    .map(|(memory, address)| (memory, address, None))
            }
            PointerBlock::Symbolic(variable) if crate::kernel::is_load_variable(variable) => {
                crate::kernel::registered_load_origin_for_variable(variable)
                    .or_else(|| crate::kernel::registered_load_for_variable(variable))
                    .zip(crate::kernel::registered_load_kind_for_variable(variable))
                    .map(|((memory, address), kind)| (memory, address, Some(kind)))
            }
            _ => None,
        };
        let Some((memory, address, kind)) = definition else {
            cache.borrow_mut().insert(cursor.block, None);
            break None;
        };
        let rewritten = rewrite_pointer(&address);
        if rewritten != address {
            let named = name_read(memory, rewritten, kind);
            cache.borrow_mut().insert(cursor.block, named.clone());
            break named;
        }
        frames.push((cursor.block, memory, kind, address.offset.clone()));
        cursor = address;
    };
    for (block, memory, kind, displacement) in frames.into_iter().rev() {
        result = result.and_then(|address| {
            name_read(
                memory,
                Pointer {
                    block: address.block,
                    offset: PointerOffsetTerm::add(address.offset, displacement),
                },
                kind,
            )
        });
        cache.borrow_mut().insert(block, result.clone());
    }
    result.map(|base| Pointer {
        block: base.block,
        offset: PointerOffsetTerm::add(base.offset, pointer.offset.clone()),
    })
}

/// Congruence inside pure-function arguments and other explicit logical
/// terms missed by the structural address rewrite. A whole symbolic pointer
/// uses capture-avoiding variable substitution; other pointer equalities use
/// exact matching and refuse internal binders whose scope is unsupported.
/// Neither path searches an ambient proof state or changes load states.
fn pointer_congruence_rewrite(
    goal: &Proposition,
    left: &Pointer,
    right: &Pointer,
) -> Option<Proposition> {
    let mut rewrite = if let PointerBlock::Symbolic(variable) = left.block
        && left.offset == PointerOffsetTerm::Constant(0)
    {
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_address_variable(
            variable, right,
        )
    } else {
        crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_exact(left, right)
    };
    // Integer machine observations retain reads as registered variables.
    // Rewrite their selected addresses, keeping the exact state and kind,
    // just as the native-condition path does for the same pointer equality.
    rewrite.enable_registered_load_resolution();
    let rewritten = rewrite.proposition(goal);
    (rewrite.refusal().is_none() && &rewritten != goal).then_some(rewritten)
}

fn pointer_offset_congruence_rewrite(
    goal: &Proposition,
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
) -> Option<Proposition> {
    let mut rewrite = super::term_rewrite::TermRewrite::for_pointer_offset_exact(left, right);
    rewrite.enable_registered_load_resolution();
    let rewritten = rewrite.proposition(goal);
    (rewrite.refusal().is_none() && &rewritten != goal).then_some(rewritten)
}

/// Why one atomic proposition was not rewritten by an equality.
#[derive(Debug)]
enum AtomicRewriteRefusal {
    /// The equality's side does not occur in the proposition: it is left as
    /// it is, and a compound goal may still rewrite elsewhere.
    Absent(String),
    /// The rewrite is not admitted here.
    Refused(String),
}

impl From<String> for AtomicRewriteRefusal {
    fn from(message: String) -> Self {
        Self::Refused(message)
    }
}

impl From<&str> for AtomicRewriteRefusal {
    fn from(message: &str) -> Self {
        Self::Refused(message.to_string())
    }
}

impl From<AtomicRewriteRefusal> for String {
    fn from(refusal: AtomicRewriteRefusal) -> Self {
        match refusal {
            AtomicRewriteRefusal::Absent(message) | AtomicRewriteRefusal::Refused(message) => {
                message
            }
        }
    }
}

// Address annotations describe a producer's object class, not the bits
// observed by a numeric equality. Keep the pointer and mask themselves
// exact; no pointer-value or memory-state identity is substituted.
fn same_address_observation(left: MachineOperandView<'_>, right: MachineOperandView<'_>) -> bool {
    fn pointer(term: MachineOperandView<'_>) -> Option<&Pointer> {
        match term {
            MachineOperandView::Legacy(term) => term.address_pointer(),
            MachineOperandView::Shared(term) => term.machine_conversion_leaf()?.address_pointer(),
        }
    }
    fn key(term: MachineOperandView<'_>) -> Option<(&Pointer, Option<u64>)> {
        if let Some(pointer) = pointer(term) {
            return Some((pointer, None));
        }
        let (MachineIntegerType::UInt64, MachineBinaryOp::BitwiseAnd, [left, right]) =
            term.binary()?
        else {
            return None;
        };
        let (pointer, mask) = if let Some(pointer) = pointer(left) {
            (pointer, right)
        } else {
            (pointer(right)?, left)
        };
        Some((pointer, Some(mask.uint64_constant()?)))
    }
    matches!((key(left), key(right)), (Some(a), Some(b)) if a == b)
}
/// Rebuild only a selected read's address, preserving its observation width.
fn rewrite_read_address(term: &MachineTerm, address: Pointer) -> MachineTerm {
    let read = crate::kernel::eval::scalar_read_observation(
        crate::kernel::MachineOperandView::Legacy(term),
    )
    .expect("selected read");
    crate::kernel::eval::scalar_read_for_exact_cell(&read.memory, &address, read.kind, read.bytes)
}

fn rewrite_term(term: &MachineTerm, from: &MachineTerm, to: &MachineTerm) -> MachineTerm {
    fn rewrite_offset(
        offset: &PointerOffsetTerm,
        from: &MachineTerm,
        to: &MachineTerm,
    ) -> PointerOffsetTerm {
        match offset {
            PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
                rewrite_offset(left, from, to),
                rewrite_offset(right, from, to),
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                crate::kernel::memory_provenance::rebuild_scaled_pointer_index(
                    rewrite_pointer_index(value, from, to),
                    *byte_width,
                    None,
                )
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => crate::kernel::memory_provenance::rebuild_scaled_pointer_index(
                rewrite_pointer_index(value, from, to),
                *byte_width,
                Some(*unsigned),
            ),
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        }
    }
    if term == from
        || same_address_observation(MachineOperandView::Legacy(term), MachineOperandView::Legacy(from))
        // Load variables and load terms of one atom are the
        // same occurrence.
        || crate::kernel::terms_have_same_canonical_form(term, from)
    {
        return to.clone();
    }
    // Widening a literal folds away the cast node. Recover only a
    // matching, checked 32-to-64-bit cast of the cited constant; the
    // replacement keeps that cast, including its signedness. Never
    // identify a full-width literal by truncating it to 32 bits.
    if let bits32_constant!(_) = from {
        let casts: &[fn(MachineTerm) -> MachineTerm] = match term {
            int64_constant!(_) => &[MachineTerm::int64_from_32, MachineTerm::int64_from_uint32],
            uint64_constant!(_) => &[MachineTerm::uint64_from_32, MachineTerm::uint64_from_int32],
            _ => &[],
        };
        for cast in casts {
            if cast(from.clone()) == *term {
                return cast(to.clone());
            }
        }
    }
    let binary = |left: &MachineTerm, right: &MachineTerm| {
        (
            Box::new(rewrite_term(left, from, to)),
            Box::new(rewrite_term(right, from, to)),
        )
    };
    // Substituting a constant can leave a two-constant operation
    // (`0 + 1` after `rewrite(len, 0)` in a `len + 1` goal); folding
    // it is deterministic arithmetic on the rewritten node only, so the
    // rewritten goal states the value the substitution denotes.
    match term {
        binary_term!(Int32, Add, left, right) => {
            let (left, right) = binary(left, right);
            match (left.as_ref(), right.as_ref()) {
                (bits32_constant!(first), bits32_constant!(second)) => {
                    MachineTerm::constant(constant_u32(*first).wrapping_add(constant_u32(*second)))
                }
                _ => binary_node!(Int32, Add, left, right),
            }
        }
        binary_term!(Int32, Subtract, left, right) => {
            let (left, right) = binary(left, right);
            match (left.as_ref(), right.as_ref()) {
                (bits32_constant!(first), bits32_constant!(second)) => {
                    MachineTerm::constant(constant_u32(*first).wrapping_sub(constant_u32(*second)))
                }
                _ => binary_node!(Int32, Subtract, left, right),
            }
        }
        binary_term!(Int32, Multiply, left, right) => {
            MachineTerm::multiply(rewrite_term(left, from, to), rewrite_term(right, from, to))
        }
        binary_term!(Int32, BitwiseAnd, left, right) => {
            MachineTerm::bitwise_and(rewrite_term(left, from, to), rewrite_term(right, from, to))
        }
        binary_term!(Int32, ShiftLeft, left, right) => {
            // The term denotes the shifted bits; signed C overflow is
            // checked separately during expression evaluation. Preserve
            // unsigned high-bit results when substitution makes both
            // operands constant.
            MachineTerm::unsigned_shift_left(
                rewrite_term(left, from, to),
                rewrite_term(right, from, to),
            )
        }
        // The same at `uint32`, whose operators and constants keep their
        // format.
        binary_term!(UInt32, Add, left, right) => {
            let (left, right) = binary(left, right);
            match (left.constant32(), right.constant32()) {
                (Some(first), Some(second)) => {
                    MachineTerm::uint32_constant(first.wrapping_add(second))
                }
                _ => binary_node!(UInt32, Add, left, right),
            }
        }
        binary_term!(UInt32, Subtract, left, right) => {
            let (left, right) = binary(left, right);
            match (left.constant32(), right.constant32()) {
                (Some(first), Some(second)) => {
                    MachineTerm::uint32_constant(first.wrapping_sub(second))
                }
                _ => binary_node!(UInt32, Subtract, left, right),
            }
        }
        binary_term!(UInt32, Multiply, left, right) => MachineTerm::multiply_at(
            MachineIntegerType::UInt32,
            rewrite_term(left, from, to),
            rewrite_term(right, from, to),
        ),
        binary_term!(UInt32, BitwiseAnd, left, right) => MachineTerm::bitwise_and_at(
            MachineIntegerType::UInt32,
            rewrite_term(left, from, to),
            rewrite_term(right, from, to),
        ),
        binary_term!(UInt32, ShiftLeft, left, right) => MachineTerm::uint32_shift_left(
            rewrite_term(left, from, to),
            rewrite_term(right, from, to),
        ),
        MachineTerm::PureFunctionApplication { name, arguments } => {
            MachineTerm::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| rewrite_term(argument, from, to))
                    .collect(),
            }
        }
        // The memory state is fixed, but its address is an ordinary
        // expression: exact equality substitution is congruent there too.
        MachineTerm::MemoryLoad(_, pointer, _) => rewrite_read_address(
            term,
            Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset(&pointer.offset, from, to),
            },
        ),
        MachineTerm::PointerAddress(pointer, class) => MachineTerm::object_pointer_address(
            Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset(&pointer.offset, from, to),
            },
            class.class(),
        ),
        MachineTerm::Variable(_) => rewrite_through_load_variable(term, &|pointer| Pointer {
            block: pointer.block.clone(),
            offset: rewrite_offset(&pointer.offset, from, to),
        })
        .unwrap_or_else(|| term.clone()),
        MachineTerm::If { .. }
        | MachineTerm::BoolCast { .. }
        | MachineTerm::RangeFold { .. }
        | MachineTerm::ClickFunctionApplication { .. }
        | MachineTerm::AlgebraicMatch { .. }
        | MachineTerm::IntegerToMachine { .. } => {
            let mut rewrite = super::term_rewrite::TermRewrite::for_bits(from, to);
            let rewritten = rewrite.bits(term);
            // The walker reports a scope it will not substitute through,
            // or exhausted work, by setting a flag and handing back a
            // placeholder constant. That placeholder is not a rewritten
            // term: keeping it replaced an unfolded `match` by `0` and
            // let `rewrite` close false goals. Declining an occurrence is
            // always a sound substitution, so the term stays as it was.
            if rewrite.refusal().is_some() {
                term.clone()
            } else {
                rewritten
            }
        }
        MachineTerm::Constant { .. } => term.clone(),
        term => match (term.as_binary(), term.as_unary()) {
            // The 32-bit word operators are rebuilt as bare nodes, the rest
            // through their smart constructors.
            (Some((op, left, right)), _) if op.is_bitvector32() => {
                op.build_raw(rewrite_term(left, from, to), rewrite_term(right, from, to))
            }
            (Some((op, left, right)), _) => {
                op.build(rewrite_term(left, from, to), rewrite_term(right, from, to))
            }
            (_, Some((op, value))) if op.is_bitvector32() => {
                op.build_raw(rewrite_term(value, from, to))
            }
            (_, Some((op, value))) => op.build(rewrite_term(value, from, to)),
            _ => unreachable!("every other variant has its own arm"),
        },
    }
}

fn rewrite_atomic_by_word_equality(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, AtomicRewriteRefusal> {
    let Proposition::ConditionIs(condition, true) = equality else {
        unreachable!("projected equality");
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(condition)
        .expect("projected word comparison");
    let mut rewrite = super::term_rewrite::TermRewrite::for_machine_operands_checked(
        view.operands[0].operand_view(),
        view.operands[1].operand_view(),
    );
    rewrite.enable_registered_load_resolution();
    let result = rewrite.proposition(goal);
    if rewrite.refusal().is_some() {
        return Err(AtomicRewriteRefusal::Refused(
            "`rewrite` cannot substitute the projected word equality within its scope or work budget".into(),
        ));
    }
    if !rewrite.changed {
        return Err(AtomicRewriteRefusal::Absent(
            "`rewrite` equality does not occur in the current goal".into(),
        ));
    }
    Ok(result)
}

fn rewrite_atomic_proposition_by_exact_equality(
    goal: &Proposition,
    equality: &Proposition,
) -> Result<Proposition, AtomicRewriteRefusal> {
    // A `Bool` equality (Stage 5, rule L-Eq) replaces its left operand by
    // its right wherever a `Bool` is read. A `Bool` value's equality with a
    // literal, `b == true` or `b == false`, lowers to the claim on `b`, and
    // replaces `b` by that literal.
    let literal = |value: bool| ConditionTerm::Constant(value);
    let bool_equation = match equality {
        Proposition::ConditionIs(ConditionTerm::BoolEqual(left, right), true) => {
            Some((left.as_ref().clone(), right.as_ref().clone()))
        }
        Proposition::ConditionIs(value, truth) if value.is_bool_value_form() => {
            Some((value.clone(), literal(*truth)))
        }
        _ => None,
    };
    if let Some((left, right)) = &bool_equation {
        let mut rewrite = super::term_rewrite::TermRewrite::for_condition_exact(left, right);
        let rewritten = rewrite.proposition(goal);
        if rewrite.refusal().is_some() {
            return Err(AtomicRewriteRefusal::Refused(
                "`Bool` rewrite exceeded its supported scope".into(),
            ));
        }
        return if rewritten != *goal {
            Ok(rewritten)
        } else {
            Err(AtomicRewriteRefusal::Absent(
                "the `Bool` equality's left side does not occur".into(),
            ))
        };
    }
    if let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) = equality
    {
        let mut rewrite = super::term_rewrite::TermRewrite::for_pointer_value_exact(left, right);
        let rewritten = rewrite.proposition(goal);
        if rewrite.refusal().is_some() {
            return Err(AtomicRewriteRefusal::Refused(
                "pointer value rewrite exceeded its supported scope".into(),
            ));
        }
        if rewritten != *goal {
            return Ok(rewritten);
        }
        return rewrite_atomic_proposition_by_exact_equality(
            goal,
            &Proposition::ConditionIs(
                ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone()),
                true,
            ),
        );
    }
    if matches!(
        goal,
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(..) | ConditionTerm::PointerEqual(..),
            _
        )
    ) && let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        },
        true,
    ) = equality
    {
        let mut rewrite = super::term_rewrite::TermRewrite::for_bits(left, right);
        let rewritten = rewrite.proposition(goal);
        if rewrite.refusal().is_none() && rewritten != *goal {
            return Ok(rewritten);
        }
    }
    fn rewrite_program_value(
        value: &ProgramValue,
        rewrite_term: &impl Fn(&MachineTerm) -> MachineTerm,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
        rewrite_shared: &impl Fn(&SharedMachineIntegerTerm) -> SharedMachineIntegerTerm,
    ) -> ProgramValue {
        match value {
            ProgramValue::PointerInteger(record) => {
                ProgramValue::PointerInteger(PointerIntegerValue {
                    kind: record.kind.clone(),
                    numeric: Box::new(rewrite_program_value(
                        &record.numeric,
                        rewrite_term,
                        rewrite_pointer,
                        rewrite_shared,
                    )),
                    pointer: Box::new(record.pointer.map_addresses(rewrite_pointer)),
                })
            }
            ProgramValue::Parameter(term) => ProgramValue::Parameter(Box::new(rewrite_algebraic(
                term,
                rewrite_term,
                rewrite_pointer,
                rewrite_shared,
            ))),
            ProgramValue::Void => ProgramValue::Void,
            ProgramValue::Bool(term) => ProgramValue::Bool(rewrite_term(term)),
            ProgramValue::Int8(term) => ProgramValue::Int8(rewrite_term(term)),
            ProgramValue::Int16(term) => ProgramValue::Int16(rewrite_term(term)),
            ProgramValue::Int32(term) => ProgramValue::Int32(rewrite_term(term)),
            ProgramValue::UInt8(term) => ProgramValue::UInt8(rewrite_term(term)),
            ProgramValue::UInt16(term) => ProgramValue::UInt16(rewrite_term(term)),
            ProgramValue::UInt32(term) => ProgramValue::UInt32(rewrite_term(term)),
            ProgramValue::Int64(term) => ProgramValue::Int64(rewrite_term(term)),
            ProgramValue::UInt64(term) => ProgramValue::UInt64(rewrite_term(term)),
            ProgramValue::Int128(term) => ProgramValue::Int128(rewrite_term(term)),
            ProgramValue::UInt128(term) => ProgramValue::UInt128(rewrite_term(term)),
            ProgramValue::Float32(term) => ProgramValue::Float32(rewrite_term(term)),
            ProgramValue::Float64(term) => ProgramValue::Float64(rewrite_term(term)),
            ProgramValue::Pointer(pointer) => {
                ProgramValue::Pointer(pointer.map_addresses(rewrite_pointer))
            }
        }
    }

    fn rewrite_algebraic(
        term: &AlgebraicTerm,
        rewrite_term: &impl Fn(&MachineTerm) -> MachineTerm,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
        rewrite_shared: &impl Fn(&SharedMachineIntegerTerm) -> SharedMachineIntegerTerm,
    ) -> AlgebraicTerm {
        let node = match &term.node {
            AlgebraicTermNode::Variable(variable) => AlgebraicTermNode::Variable(*variable),
            AlgebraicTermNode::MemoryLoad { memory, pointer } => AlgebraicTermNode::MemoryLoad {
                memory: memory.clone(),
                pointer: Box::new(rewrite_pointer(pointer)),
            },
            AlgebraicTermNode::Constructor { variant, fields } => AlgebraicTermNode::Constructor {
                variant: variant.clone(),
                fields: fields
                    .iter()
                    .map(|field| {
                        rewrite_algebraic_value(
                            field,
                            rewrite_term,
                            rewrite_pointer,
                            rewrite_shared,
                        )
                    })
                    .collect(),
            },
            AlgebraicTermNode::Match { scrutinee, arms } => AlgebraicTermNode::Match {
                scrutinee: Box::new(rewrite_algebraic(
                    scrutinee,
                    rewrite_term,
                    rewrite_pointer,
                    rewrite_shared,
                )),
                arms: arms
                    .iter()
                    .map(|arm| AlgebraicResultMatchArm {
                        binding_names: arm.binding_names.clone(),
                        variant: arm.variant.clone(),
                        bindings: arm
                            .bindings
                            .iter()
                            .map(|binding| {
                                rewrite_algebraic_value(
                                    binding,
                                    rewrite_term,
                                    rewrite_pointer,
                                    rewrite_shared,
                                )
                            })
                            .collect(),
                        body: rewrite_algebraic(
                            &arm.body,
                            rewrite_term,
                            rewrite_pointer,
                            rewrite_shared,
                        ),
                    })
                    .collect(),
            },
            AlgebraicTermNode::PureFunctionApplication { name, arguments } => {
                AlgebraicTermNode::PureFunctionApplication {
                    name: name.clone(),
                    arguments: arguments
                        .iter()
                        .map(|argument| match argument {
                            PureFunctionArgument::SharedMachine(value) => {
                                PureFunctionArgument::SharedMachine(rewrite_shared(value))
                            }
                            PureFunctionArgument::Value(value) => {
                                PureFunctionArgument::Value(rewrite_program_value(
                                    value,
                                    rewrite_term,
                                    rewrite_pointer,
                                    rewrite_shared,
                                ))
                            }
                            PureFunctionArgument::Algebraic(value) => {
                                PureFunctionArgument::Algebraic(rewrite_algebraic(
                                    value,
                                    rewrite_term,
                                    rewrite_pointer,
                                    rewrite_shared,
                                ))
                            }
                            PureFunctionArgument::Integer(value) => {
                                PureFunctionArgument::Integer(value.clone())
                            }
                            PureFunctionArgument::ArrayRef {
                                memory,
                                pointer,
                                element_type,
                            } => PureFunctionArgument::ArrayRef {
                                memory: memory.clone(),
                                pointer: rewrite_program_value(
                                    pointer,
                                    rewrite_term,
                                    rewrite_pointer,
                                    rewrite_shared,
                                ),
                                element_type: *element_type,
                            },
                        })
                        .collect(),
                }
            }
            AlgebraicTermNode::If {
                condition,
                then_term,
                else_term,
            } => {
                return AlgebraicTerm::if_then_else(
                    crate::kernel::rewrite_condition_through_bits(condition, rewrite_term),
                    rewrite_algebraic(then_term, rewrite_term, rewrite_pointer, rewrite_shared),
                    rewrite_algebraic(else_term, rewrite_term, rewrite_pointer, rewrite_shared),
                );
            }
        };
        AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node,
        }
    }

    fn rewrite_algebraic_value(
        value: &AlgebraicValue,
        rewrite_term: &impl Fn(&MachineTerm) -> MachineTerm,
        rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
        rewrite_shared: &impl Fn(&SharedMachineIntegerTerm) -> SharedMachineIntegerTerm,
    ) -> AlgebraicValue {
        match value {
            AlgebraicValue::Program(value) => AlgebraicValue::Program(rewrite_program_value(
                value,
                rewrite_term,
                rewrite_pointer,
                rewrite_shared,
            )),
            AlgebraicValue::Integer(value) => AlgebraicValue::Integer(value.clone()),
            AlgebraicValue::Algebraic(value) => AlgebraicValue::Algebraic(rewrite_algebraic(
                value,
                rewrite_term,
                rewrite_pointer,
                rewrite_shared,
            )),
        }
    }

    if let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) = equality {
        let mut rewrite = super::term_rewrite::TermRewrite::for_integer_exact(left, right);
        let rewritten = rewrite.proposition(goal);
        match rewrite.refusal() {
            Some(super::term_rewrite::RewriteRefusal::WorkExhausted) => {
                return Err(
                    "`rewrite` exhausted its work budget while rewriting Integer terms".into(),
                );
            }
            Some(super::term_rewrite::RewriteRefusal::UnsupportedScope) => {
                return Err("`rewrite` cannot substitute an Integer equality through an internal fold or match binder".into());
            }
            None => {}
        }
        if !rewrite.changed {
            return Err(AtomicRewriteRefusal::Absent(
                "`rewrite` equality does not occur in the current goal".to_string(),
            ));
        }
        return Ok(rewritten);
    }

    if let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = equality {
        let mut rewrite = super::term_rewrite::TermRewrite::new(left, right);
        let rewritten = match goal {
            Proposition::Equal(a, b) => Proposition::Equal(rewrite.term(a), rewrite.term(b)),
            Proposition::ConditionIs(c, expected) => {
                Proposition::ConditionIs(rewrite.condition(c), *expected)
            }
            _ => {
                return Err(AtomicRewriteRefusal::Absent(
                    "`rewrite` algebraic equality does not occur in this goal".to_string(),
                ));
            }
        };
        if rewrite.refusal().is_some() {
            // A refused scope or exhausted work leaves placeholders in the
            // walker's result; it is not a rewritten goal.
            return Err(
                "`rewrite` cannot substitute this equality through a binder in the current goal"
                    .into(),
            );
        }
        if !rewrite.changed {
            return Err(AtomicRewriteRefusal::Absent(
                "`rewrite` equality does not occur in the current goal".to_string(),
            ));
        }
        return Ok(rewritten);
    }

    if let Proposition::ConditionIs(condition, true) = equality
        && let Some((left, right)) = condition.pointer_offset_sides()
    {
        fn rewrite_offset(
            offset: &PointerOffsetTerm,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> PointerOffsetTerm {
            if offset == left
                // Load variables and load terms of one atom are
                // the same occurrence.
                || crate::kernel::offsets_have_same_canonical_form(offset, left)
            {
                return right.clone();
            }
            match offset {
                PointerOffsetTerm::Add(first, second) => PointerOffsetTerm::add(
                    rewrite_offset(first, left, right),
                    rewrite_offset(second, left, right),
                ),
                // A scaled index may be a load variable whose own address
                // names the rewritten offset (`p->q->cells[i]` under
                // `p->q == r`): rewrite through it, as through the outer
                // load. Each level is the registered address of one load.
                PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                    let rewritten = crate::kernel::memory_provenance::map_shared_pointer_index(
                        value,
                        |leaf| Some(rewrite_term_offset(leaf, left, right)),
                        rebuild_transported_machine_node,
                    )
                    .unwrap_or_else(|| value.clone());
                    if crate::kernel::memory_provenance::pointer_index_syntax_equal(
                        value, &rewritten,
                    ) {
                        offset.clone()
                    } else {
                        crate::kernel::memory_provenance::rebuild_scaled_pointer_index(
                            rewritten,
                            *byte_width,
                            None,
                        )
                    }
                }
                PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned,
                } => {
                    let rewritten = crate::kernel::memory_provenance::map_shared_pointer_index(
                        value,
                        |leaf| Some(rewrite_term_offset(leaf, left, right)),
                        rebuild_transported_machine_node,
                    )
                    .unwrap_or_else(|| value.clone());
                    if crate::kernel::memory_provenance::pointer_index_syntax_equal(
                        value, &rewritten,
                    ) {
                        offset.clone()
                    } else {
                        crate::kernel::memory_provenance::rebuild_scaled_pointer_index(
                            rewritten,
                            *byte_width,
                            Some(*unsigned),
                        )
                    }
                }
                PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
            }
        }
        fn rewrite_term_offset(
            term: &MachineTerm,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> MachineTerm {
            let rewrite_pointer = |pointer: &Pointer| Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset(&pointer.offset, left, right),
            };
            match term {
                MachineTerm::PureFunctionApplication { name, arguments } => {
                    MachineTerm::PureFunctionApplication {
                        name: name.clone(),
                        arguments: arguments
                            .iter()
                            .map(|argument| rewrite_term_offset(argument, left, right))
                            .collect(),
                    }
                }
                MachineTerm::MemoryLoad(_, pointer, _) => {
                    rewrite_read_address(term, rewrite_pointer(pointer))
                }
                MachineTerm::PointerAddress(pointer, class) => {
                    MachineTerm::object_pointer_address(rewrite_pointer(pointer), class.class())
                }
                MachineTerm::Variable(_) => rewrite_through_load_variable(term, &rewrite_pointer)
                    .unwrap_or_else(|| term.clone()),
                MachineTerm::If { .. }
                | MachineTerm::BoolCast { .. }
                | MachineTerm::RangeFold { .. }
                | MachineTerm::ClickFunctionApplication { .. }
                | MachineTerm::AlgebraicMatch { .. }
                | MachineTerm::IntegerToMachine { .. }
                | MachineTerm::Constant { .. } => term.clone(),
                term => match (term.as_binary(), term.as_unary()) {
                    // The 32-bit word operators are rebuilt as bare nodes, the rest
                    // through their smart constructors.
                    (Some((op, lhs, rhs)), _) if op.is_bitvector32() => op.build_raw(
                        rewrite_term_offset(lhs, left, right),
                        rewrite_term_offset(rhs, left, right),
                    ),
                    (Some((op, lhs, rhs)), _) => op.build(
                        rewrite_term_offset(lhs, left, right),
                        rewrite_term_offset(rhs, left, right),
                    ),
                    (_, Some((op, operand))) if op.is_bitvector32() => {
                        op.build_raw(rewrite_term_offset(operand, left, right))
                    }
                    (_, Some((op, operand))) => op.build(rewrite_term_offset(operand, left, right)),
                    _ => unreachable!("every other variant has its own arm"),
                },
            }
        }
        fn rewrite_resource_offset(
            resource: &Resource,
            left: &PointerOffsetTerm,
            right: &PointerOffsetTerm,
        ) -> Resource {
            match resource {
                Resource::Star(pair) => Resource::star(
                    rewrite_resource_offset(&pair.0, left, right),
                    rewrite_resource_offset(&pair.1, left, right),
                ),
                Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp => resource.clone(),
                Resource::Memory(range) => Resource::Memory(range.with_bounds(
                    Pointer {
                        block: range.base().block.clone(),
                        offset: rewrite_offset(&range.base().offset, left, right),
                    },
                    rewrite_term_offset(range.bound_terms().0, left, right),
                    rewrite_term_offset(range.bound_terms().1, left, right),
                )),
                Resource::Composite { .. }
                | Resource::Token { .. }
                | Resource::PopulationAuthority(_)
                | Resource::Instance(_)
                | Resource::MutexGuard(_)
                | Resource::MutexLive(_)
                | Resource::MutexUse(_)
                | Resource::Publication(_)
                | Resource::Iterated(_) => resource.clone(),
            }
        }
        let rewritten = match goal {
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide,
            } => Proposition::MemoryLoadable {
                // Same-block pointer equalities use offsets rather than the
                // PointerEqual carrier. Substitute the selected address while
                // retaining the exact state and readable byte extent.
                memory: memory.clone(),
                base: Pointer {
                    block: base.block.clone(),
                    offset: rewrite_offset(&base.offset, left, right),
                },
                bytes: bytes.clone(),
                wide: *wide,
            },
            Proposition::ConditionIs(
                ConditionTerm::PointerOffsetEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                ConditionTerm::PointerOffsetEqual(
                    Box::new(rewrite_offset(goal_left, left, right)),
                    Box::new(rewrite_offset(goal_right, left, right)),
                ),
                *expected,
            ),
            Proposition::ConditionIs(
                ConditionTerm::PointerEqual(goal_left, goal_right),
                expected,
            ) => {
                let rewrite_pointer = |pointer: &Pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, left, right),
                };
                Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(
                        rewrite_pointer(goal_left),
                        rewrite_pointer(goal_right),
                    ),
                    *expected,
                )
            }
            Proposition::ConditionIs(condition, expected) => {
                let rewrite_term = |term: &MachineTerm| rewrite_term_offset(term, left, right);
                let rewritten = match condition {
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left,
                        right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(rewrite_term(left)),
                        right: Box::new(rewrite_term(right)),
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left,
                        right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(rewrite_term(left)),
                        right: Box::new(rewrite_term(right)),
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left,
                        right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(rewrite_term(left)),
                        right: Box::new(rewrite_term(right)),
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left,
                        right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(rewrite_term(left)),
                        right: Box::new(rewrite_term(right)),
                    },
                    ConditionTerm::Compare {
                        format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    } => ConditionTerm::Compare {
                        format: *format,
                        relation: CompareRelation::Equal,
                        left: Box::new(rewrite_term(left)),
                        right: Box::new(rewrite_term(right)),
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: Box::new(rewrite_term(left)),
                        right: Box::new(rewrite_term(right)),
                    },
                    _ => {
                        return pointer_offset_congruence_rewrite(goal, left, right).ok_or_else(
                            || {
                                AtomicRewriteRefusal::Absent(
                                    "`rewrite` pointer-offset equality does not occur in this goal"
                                        .to_string(),
                                )
                            },
                        );
                    }
                };
                Proposition::ConditionIs(rewritten, *expected)
            }
            Proposition::ResourceSeparate {
                left: goal_left,
                right: goal_right,
            } => Proposition::ResourceSeparate {
                left: Box::new(rewrite_resource_offset(goal_left, left, right)),
                right: Box::new(rewrite_resource_offset(goal_right, left, right)),
            },
            Proposition::ResourceViewable { memory, resource } => crate::kernel::resource_viewable(
                memory,
                rewrite_resource_offset(resource, left, right),
            ),
            Proposition::ResourceContains { parent, child } => Proposition::ResourceContains {
                parent: Box::new(rewrite_resource_offset(parent, left, right)),
                child: Box::new(rewrite_resource_offset(child, left, right)),
            },
            Proposition::Equal(Term::Algebraic(goal_left), Term::Algebraic(goal_right)) => {
                let rewrite_term = |term: &MachineTerm| rewrite_term_offset(term, left, right);
                let rewrite_pointer = |pointer: &Pointer| Pointer {
                    block: pointer.block.clone(),
                    offset: rewrite_offset(&pointer.offset, left, right),
                };
                let rewrite_shared = |value: &SharedMachineIntegerTerm| {
                    crate::kernel::memory_provenance::map_shared_pointer_index(
                        value,
                        |leaf| Some(rewrite_term(leaf)),
                        rebuild_transported_machine_node,
                    )
                    .unwrap_or_else(|| value.clone())
                };
                Proposition::Equal(
                    Term::Algebraic(rewrite_algebraic(
                        goal_left,
                        &rewrite_term,
                        &rewrite_pointer,
                        &rewrite_shared,
                    )),
                    Term::Algebraic(rewrite_algebraic(
                        goal_right,
                        &rewrite_term,
                        &rewrite_pointer,
                        &rewrite_shared,
                    )),
                )
            }
            _ => {
                return pointer_offset_congruence_rewrite(goal, left, right).ok_or_else(|| {
                    AtomicRewriteRefusal::Absent(
                        "`rewrite` pointer-offset equality does not occur in this goal".to_string(),
                    )
                });
            }
        };
        if &rewritten == goal {
            return pointer_offset_congruence_rewrite(goal, left, right).ok_or_else(|| {
                AtomicRewriteRefusal::Absent(
                    "`rewrite` equality does not occur in the current goal".to_string(),
                )
            });
        }
        return Ok(rewritten);
    }
    if let Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) = equality {
        // A field or array access keeps its base pointer's block and adds a
        // displacement. An equality of the bases therefore also rewrites the
        // address of that access, with the same displacement on the right.
        // Match one structural suffix; do not search the ambient pointer
        // equalities or change the memory state of a load.
        fn offset_after_base(
            address: &PointerOffsetTerm,
            base: &PointerOffsetTerm,
        ) -> Option<PointerOffsetTerm> {
            if base == &PointerOffsetTerm::Constant(0) {
                return Some(address.clone());
            }
            // Keep parent links rather than cloning a growing suffix at each
            // Add node. A deeply nested address costs one walk plus one
            // construction of the matched displacement.
            struct OffsetNode<'a> {
                offset: &'a PointerOffsetTerm,
                parent: Option<usize>,
                sibling: Option<&'a PointerOffsetTerm>,
            }
            let mut nodes = vec![OffsetNode {
                offset: address,
                parent: None,
                sibling: None,
            }];
            let mut pending = vec![0];
            while let Some(index) = pending.pop() {
                let offset = nodes[index].offset;
                let difference = if offset == base {
                    Some(PointerOffsetTerm::Constant(0))
                } else if let (
                    PointerOffsetTerm::Constant(address),
                    PointerOffsetTerm::Constant(base),
                ) = (offset, base)
                {
                    address.checked_sub(*base).map(PointerOffsetTerm::Constant)
                } else {
                    None
                };
                if let Some(mut difference) = difference {
                    let mut cursor = index;
                    while let Some(parent) = nodes[cursor].parent {
                        difference =
                            add_pointer_offsets(difference, nodes[cursor].sibling?.clone())?;
                        cursor = parent;
                    }
                    return Some(difference);
                }
                if let PointerOffsetTerm::Add(left, right) = offset {
                    let left_index = nodes.len();
                    nodes.push(OffsetNode {
                        offset: left,
                        parent: Some(index),
                        sibling: Some(right),
                    });
                    let right_index = nodes.len();
                    nodes.push(OffsetNode {
                        offset: right,
                        parent: Some(index),
                        sibling: Some(left),
                    });
                    pending.push(right_index);
                    pending.push(left_index);
                }
            }
            None
        }
        fn add_pointer_offsets(
            left: PointerOffsetTerm,
            right: PointerOffsetTerm,
        ) -> Option<PointerOffsetTerm> {
            use PointerOffsetTerm::{Add, Constant};
            match (left, right) {
                (Constant(0), other) | (other, Constant(0)) => Some(other),
                (Constant(left), Constant(right)) => left.checked_add(right).map(Constant),
                (Add(base, trailing), Constant(right))
                    if matches!(trailing.as_ref(), Constant(_)) =>
                {
                    let Constant(trailing) = *trailing else {
                        unreachable!()
                    };
                    let combined = trailing.checked_add(right)?;
                    if combined == 0 {
                        Some(*base)
                    } else {
                        Some(Add(base, Box::new(Constant(combined))))
                    }
                }
                (left, right) => Some(Add(Box::new(left), Box::new(right))),
            }
        }
        let rewrite_pointer_directly = |pointer: &Pointer| {
            if pointer == left.as_ref() {
                return right.as_ref().clone();
            }
            if pointer.block != left.block {
                return pointer.clone();
            }
            let Some(displacement) = offset_after_base(&pointer.offset, &left.offset) else {
                return pointer.clone();
            };
            let Some(offset) = add_pointer_offsets(right.offset.clone(), displacement) else {
                return pointer.clone();
            };
            Pointer {
                block: right.block.clone(),
                offset,
            }
        };
        let read_rewrites = PointerReadRewrites::default();
        let rewrite_pointer = |pointer: &Pointer| {
            if pointer == left.as_ref() {
                return right.as_ref().clone();
            }
            let rewritten = rewrite_pointer_directly(pointer);
            if &rewritten != pointer {
                return rewritten;
            }
            rewrite_through_loaded_pointer_block(pointer, &rewrite_pointer_directly, &read_rewrites)
                .unwrap_or(rewritten)
        };
        // A pointer equality also rewrites the subject of a load: replacing
        // the loaded pointer with its proven-equal form is exact term
        // congruence, with work bounded by the goal's size.
        fn rewrite_load_pointers(
            term: &MachineTerm,
            rewrite_pointer: &impl Fn(&Pointer) -> Pointer,
        ) -> MachineTerm {
            let binary = |left_term: &MachineTerm, right_term: &MachineTerm| {
                (
                    Box::new(rewrite_load_pointers(left_term, rewrite_pointer)),
                    Box::new(rewrite_load_pointers(right_term, rewrite_pointer)),
                )
            };
            match term {
                MachineTerm::MemoryLoad(_, pointer, _) => {
                    rewrite_read_address(term, rewrite_pointer(pointer))
                }
                MachineTerm::Variable(_) => rewrite_through_load_variable(term, rewrite_pointer)
                    .unwrap_or_else(|| term.clone()),
                binary_term!(Bits32 @ format32, Add, left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    binary_node!(@ *format32, Add, left, right)
                }
                binary_term!(Bits32 @ format32, Subtract, left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    binary_node!(@ *format32, Subtract, left, right)
                }
                binary_term!(Bits32 @ format32, Multiply, left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    binary_node!(@ *format32, Multiply, left, right)
                }
                binary_term!(Int32, Divide, left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    binary_node!(Int32, Divide, left, right)
                }
                binary_term!(Int32, Remainder, left_term, right_term) => {
                    let (left, right) = binary(left_term, right_term);
                    binary_node!(Int32, Remainder, left, right)
                }
                _ => term.clone(),
            }
        }
        let rewritten = match goal {
            Proposition::MemoryLoadable {
                memory,
                base,
                bytes,
                wide,
            } => {
                Proposition::MemoryLoadable {
                    // Clone only shared state roots. Equality changes the
                    // selected address, never the memory or view extent.
                    memory: memory.clone(),
                    base: rewrite_pointer(base),
                    bytes: bytes.clone(),
                    wide: *wide,
                }
            }
            Proposition::ConditionIs(
                ConditionTerm::PointerEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                // Replacing one side can land both pointers in the same
                // block, and a same-block pointer equality is carried
                // everywhere else as the equality of its offsets. Rebuild
                // through the canonicalizing constructor so the rewritten
                // goal is the term an ordinary lowering would produce and a
                // later `known` or `normalize() using` can see it.
                ConditionTerm::pointer_equal(
                    rewrite_pointer(goal_left),
                    rewrite_pointer(goal_right),
                ),
                *expected,
            ),
            Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(goal_left, goal_right),
                expected,
            ) => Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(
                    Box::new(goal_left.map_addresses(&rewrite_pointer)),
                    Box::new(goal_right.map_addresses(&rewrite_pointer)),
                ),
                *expected,
            ),
            Proposition::ConditionIs(condition, expected) => {
                let rewrite_term =
                    |term: &MachineTerm| rewrite_load_pointers(term, &rewrite_pointer);
                let rewritten = match condition {
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: goal_left,
                        right: goal_right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(rewrite_term(goal_left)),
                        right: Box::new(rewrite_term(goal_right)),
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: goal_left,
                        right: goal_right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(rewrite_term(goal_left)),
                        right: Box::new(rewrite_term(goal_right)),
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: goal_left,
                        right: goal_right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterThan,
                        left: Box::new(rewrite_term(goal_left)),
                        right: Box::new(rewrite_term(goal_right)),
                    },
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: goal_left,
                        right: goal_right,
                    } => ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(rewrite_term(goal_left)),
                        right: Box::new(rewrite_term(goal_right)),
                    },
                    ConditionTerm::Compare {
                        format: format @ (MachineIntegerType::Int32 | MachineIntegerType::UInt32),
                        relation: CompareRelation::Equal,
                        left: goal_left,
                        right: goal_right,
                    } => ConditionTerm::Compare {
                        format: *format,
                        relation: CompareRelation::Equal,
                        left: Box::new(rewrite_term(goal_left)),
                        right: Box::new(rewrite_term(goal_right)),
                    },
                    // A native 8- or 16-bit comparison keeps its format.
                    ConditionTerm::Compare {
                        format,
                        relation,
                        left: goal_left,
                        right: goal_right,
                    } if format.format().bits() < 32 => ConditionTerm::Compare {
                        format: *format,
                        relation: *relation,
                        left: Box::new(rewrite_term(goal_left)),
                        right: Box::new(rewrite_term(goal_right)),
                    },
                    _ => {
                        return pointer_congruence_rewrite(goal, left, right).ok_or_else(|| {
                            AtomicRewriteRefusal::Absent(
                                "`rewrite` pointer equality does not occur in this goal"
                                    .to_string(),
                            )
                        });
                    }
                };
                Proposition::ConditionIs(rewritten, *expected)
            }
            Proposition::Equal(Term::Algebraic(goal_left), Term::Algebraic(goal_right)) => {
                let rewrite_term =
                    |term: &MachineTerm| rewrite_load_pointers(term, &rewrite_pointer);
                let rewrite_shared = |value: &SharedMachineIntegerTerm| {
                    crate::kernel::memory_provenance::map_shared_pointer_index(
                        value,
                        |leaf| Some(rewrite_term(leaf)),
                        rebuild_transported_machine_node,
                    )
                    .unwrap_or_else(|| value.clone())
                };
                Proposition::Equal(
                    Term::Algebraic(rewrite_algebraic(
                        goal_left,
                        &rewrite_term,
                        &rewrite_pointer,
                        &rewrite_shared,
                    )),
                    Term::Algebraic(rewrite_algebraic(
                        goal_right,
                        &rewrite_term,
                        &rewrite_pointer,
                        &rewrite_shared,
                    )),
                )
            }
            _ => {
                return pointer_congruence_rewrite(goal, left, right)
                    .ok_or_else(|| "`rewrite` pointer equality expects a condition goal".into());
            }
        };
        if &rewritten == goal {
            return pointer_congruence_rewrite(goal, left, right).ok_or_else(|| {
                AtomicRewriteRefusal::Absent(
                    "`rewrite` equality does not occur in the current goal".to_string(),
                )
            });
        }
        return Ok(rewritten);
    }
    let (left, right) = match equality {
        Proposition::ConditionIs(ConditionTerm::Compare { format: MachineIntegerType::Int32 | MachineIntegerType::UInt32, relation: CompareRelation::Equal, left, right }, true) => {
            (left, right)
        }
        Proposition::ConditionIs(ConditionTerm::Compare { format: MachineIntegerType::Int64, relation: CompareRelation::Equal, left, right }, true) => {
            (left, right)
        }
        // A native 8- or 16-bit equality equates two values of its width.
        Proposition::ConditionIs(ConditionTerm::Compare { format, relation: CompareRelation::Equal, left, right }, true)
            if format.format().bits() < 32 =>
        {
            (left, right)
        }
        _ => return Err("`rewrite` expects a mathematical Integer, native 32-bit/64-bit, pointer, or algebraic equality".into()),

    };
    fn rewrite_offset_term(
        offset: &PointerOffsetTerm,
        from: &MachineTerm,
        to: &MachineTerm,
    ) -> PointerOffsetTerm {
        match offset {
            PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
                rewrite_offset_term(left, from, to),
                rewrite_offset_term(right, from, to),
            ),
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                crate::kernel::memory_provenance::rebuild_scaled_pointer_index(
                    rewrite_pointer_index(value, from, to),
                    *byte_width,
                    None,
                )
            }
            PointerOffsetTerm::Int64Scaled {
                value,
                byte_width,
                unsigned,
            } => crate::kernel::memory_provenance::rebuild_scaled_pointer_index(
                rewrite_pointer_index(value, from, to),
                *byte_width,
                Some(*unsigned),
            ),
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        }
    }

    // A mathematical observation of a machine value is still congruent under
    // a checked equality for that machine value.  Keep this bridge narrow:
    // root machine observations, scalar application arguments, and
    // Int32 range-fold endpoints retain their direct substitutions. Arithmetic
    // uses the shared checked, scope-aware walker; a refusal keeps the original
    // term, never a partial result. Re-interning through `from_machine` folds a
    // rewritten constant to the ordinary mathematical constant while
    // retaining the carrier when it remains symbolic.
    fn rewrite_integer_observation(
        term: &SharedIntegerTerm,
        from: &MachineTerm,
        to: &MachineTerm,
    ) -> SharedIntegerTerm {
        match term.as_ref() {
            IntegerTerm::Machine(machine) => {
                if let Some(root) = machine.shared_operand()
                    && let Some(value) =
                        shared::rewrite(root, from, to, |leaf| rewrite_term(leaf, from, to))
                {
                    if value == *root {
                        return term.clone();
                    }
                    let observed = SharedMachineIntegerTerm::observe_shared(machine.ty(), value)
                        .expect("retained rewritten observation");
                    return observed
                        .operand_view()
                        .observe(machine.ty())
                        .unwrap_or_else(|| IntegerTerm::Machine(observed.clone()))
                        .into();
                }
                if crate::instrumentation::deadline_exceeded() {
                    return term.clone();
                }
                // An opaque replacement can leave the shared producer fragment.
                // Keep that explicit compatibility output boundary.
                let value = rewrite_term(machine.value(), from, to);
                if value == *machine.value() {
                    return term.clone();
                }
                IntegerTerm::from_machine(machine.ty(), value.clone())
                    .unwrap_or_else(|| {
                        IntegerTerm::Machine(SharedMachineIntegerTerm::intern(machine.ty(), value))
                    })
                    .into()
            }
            IntegerTerm::PureFunctionApplication(application) => {
                // Rewrite scalar arguments, preserving captured array memory
                // and its element type. No state contents are traversed.
                let arguments = application
                    .arguments()
                    .iter()
                    .map(|argument| {
                        let value = match argument {
                            PureFunctionArgument::SharedMachine(value) => {
                                return PureFunctionArgument::SharedMachine(rewrite_pointer_index(
                                    value, from, to,
                                ));
                            }
                            PureFunctionArgument::Value(ProgramValue::Int32(value)) => {
                                ProgramValue::Int32(rewrite_term(value, from, to))
                            }
                            PureFunctionArgument::Value(ProgramValue::UInt32(value)) => {
                                ProgramValue::UInt32(rewrite_term(value, from, to))
                            }
                            PureFunctionArgument::Value(ProgramValue::Int64(value)) => {
                                ProgramValue::Int64(rewrite_term(value, from, to))
                            }
                            PureFunctionArgument::Value(ProgramValue::UInt64(value)) => {
                                ProgramValue::UInt64(rewrite_term(value, from, to))
                            }
                            _ => return argument.clone(),
                        };
                        PureFunctionArgument::Value(value)
                    })
                    .collect();
                IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                    application.name().to_string(),
                    arguments,
                ))
                .into()
            }
            IntegerTerm::RangeFold {
                index:
                    index @ (IntegerRangeFoldIndex::Int32 { start, end }
                    | IntegerRangeFoldIndex::UInt64 { start, end }),
                initial,
                accumulator,
                item,
                body,
            } => {
                let endpoint = |endpoint: &SharedIntegerRangeEndpoint| {
                    if let Some(root) = endpoint.machine_operand().shared_operand()
                        && let Some(value) =
                            shared::rewrite(root, from, to, |leaf| rewrite_term(leaf, from, to))
                    {
                        return endpoint
                            .with_shared_operand(value)
                            .expect("retained endpoint rewrite");
                    }
                    if crate::instrumentation::deadline_exceeded() {
                        return endpoint.clone();
                    }
                    SharedIntegerRangeEndpoint::intern(rewrite_term(endpoint.value(), from, to))
                };
                let rewritten_start = endpoint(start);
                let rewritten_end = endpoint(end);
                if rewritten_start == *start && rewritten_end == *end {
                    return term.clone();
                }
                IntegerTerm::RangeFold {
                    index: match index {
                        IntegerRangeFoldIndex::Int32 { .. } => IntegerRangeFoldIndex::Int32 {
                            start: rewritten_start,
                            end: rewritten_end,
                        },
                        IntegerRangeFoldIndex::UInt64 { .. } => IntegerRangeFoldIndex::UInt64 {
                            start: rewritten_start,
                            end: rewritten_end,
                        },
                        _ => unreachable!(),
                    },
                    initial: initial.clone(),
                    accumulator: *accumulator,
                    item: *item,
                    body: body.clone(),
                }
                .into()
            }
            _ => {
                let mut rewrite = super::term_rewrite::TermRewrite::for_bits_checked(from, to);
                let rewritten = rewrite.integer(term.as_ref());
                if rewrite.refusal().is_some() {
                    term.clone()
                } else {
                    rewritten.into()
                }
            }
        }
    }

    let full_width_equality = matches!(
        equality,
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: _,
                right: _
            },
            true
        )
    );
    let rewrite_range_bound = |range: &MemoryRange, bound: &MachineTerm| {
        // A narrow equality cannot replace the complete value of a native
        // bound, even when both are represented by the same term variant.
        if range.wide_bounds().is_some() && !full_width_equality {
            bound.clone()
        } else {
            rewrite_term(bound, left, right)
        }
    };
    let rewrite_resource_leaf = |resource: &Resource| match resource {
        Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_) => {
            resource.clone()
        }
        Resource::Memory(range) => Resource::Memory(range.with_bounds(
            Pointer {
                block: range.base().block.clone(),
                offset: rewrite_offset_term(&range.base().offset, left, right),
            },
            rewrite_range_bound(range, range.bound_terms().0),
            rewrite_range_bound(range, range.bound_terms().1),
        )),
        Resource::Composite { .. }
        | Resource::Token { .. }
        | Resource::PopulationAuthority(_)
        | Resource::Instance(_)
        | Resource::MutexGuard(_)
        | Resource::MutexLive(_)
        | Resource::MutexUse(_)
        | Resource::Publication(_)
        | Resource::Iterated(_) => resource.clone(),
    };
    fn map_resource(resource: &Resource, leaf: &impl Fn(&Resource) -> Resource) -> Resource {
        match resource {
            Resource::Star(pair) => {
                Resource::star(map_resource(&pair.0, leaf), map_resource(&pair.1, leaf))
            }
            other => leaf(other),
        }
    }
    let rewrite_resource_term =
        |resource: &Resource| map_resource(resource, &rewrite_resource_leaf);
    let rewritten = match goal {
        Proposition::ConditionIs(condition, expected) => {
            let rewritten_condition = if let Some((operator, goal_left, goal_right)) =
                condition.as_bitvector_comparison()
            {
                operator.build_raw(
                    rewrite_term(goal_left, left, right),
                    rewrite_term(goal_right, left, right),
                )
            } else {
                match condition {
                    // A literal guard contains no machine occurrence. Keep it
                    // while the compound rewriter visits the other leaves.
                    ConditionTerm::Constant(_) => condition.clone(),
                    // `to_integer(machine)` is represented as an Integer machine
                    // observation.  Rewrite its selected machine payload through
                    // the already checked C equality, then let the normal
                    // Integer constructor fold a constant observation.
                    ConditionTerm::IntegerEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerLessThan(goal_left, goal_right) => {
                        ConditionTerm::IntegerLessThan(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerLessEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerLessEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerGreaterThan(goal_left, goal_right) => {
                        ConditionTerm::IntegerGreaterThan(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerGreaterEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerGreaterEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    ConditionTerm::IntegerNotEqual(goal_left, goal_right) => {
                        ConditionTerm::IntegerNotEqual(
                            rewrite_integer_observation(goal_left, left, right),
                            rewrite_integer_observation(goal_right, left, right),
                        )
                    }
                    // Pointer goals contain the same int32 terms inside their
                    // offsets; substituting the proven equality there is the same
                    // exact term congruence, with work bounded by the goal.
                    ConditionTerm::PointerOffsetEqual(goal_left, goal_right) => {
                        ConditionTerm::PointerOffsetEqual(
                            Box::new(rewrite_offset_term(goal_left, left, right)),
                            Box::new(rewrite_offset_term(goal_right, left, right)),
                        )
                    }
                    ConditionTerm::PointerEqual(goal_left, goal_right) => {
                        let rewrite_pointer = |pointer: &Pointer| Pointer {
                            block: pointer.block.clone(),
                            offset: rewrite_offset_term(&pointer.offset, left, right),
                        };
                        ConditionTerm::pointer_equal(
                            rewrite_pointer(goal_left),
                            rewrite_pointer(goal_right),
                        )
                    }
                    _ => {
                        return Err("`rewrite` cannot substitute this native equality in the selected condition".into());
                    }
                }
            };
            // Rewriting can expose an address mask that the normal
            // comparison constructor canonicalizes. Present that same form.
            let rewritten_condition = if rewritten_condition.as_pointer_alignment().is_some() {
                match rewritten_condition {
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left,
                        right,
                    } => ConditionTerm::int64_equal(*left, *right),
                    other => other,
                }
            } else {
                rewritten_condition
            };
            Proposition::ConditionIs(rewritten_condition, *expected)
        }
        Proposition::ResourceSeparate {
            left: goal_left,
            right: goal_right,
        } => Proposition::ResourceSeparate {
            left: Box::new(rewrite_resource_term(goal_left)),
            right: Box::new(rewrite_resource_term(goal_right)),
        },
        Proposition::ResourceViewable { memory, resource } => {
            crate::kernel::resource_viewable(memory, rewrite_resource_term(resource))
        }
        Proposition::ResourceContains { parent, child } => Proposition::ResourceContains {
            parent: Box::new(rewrite_resource_term(parent)),
            child: Box::new(rewrite_resource_term(child)),
        },
        Proposition::MemoryReadDefined {
            memory,
            pointer,
            value_type,
        } => Proposition::MemoryReadDefined {
            memory: memory.clone(),
            pointer: Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset_term(&pointer.offset, left, right),
            },
            value_type: *value_type,
        },
        Proposition::MemoryLoadable {
            memory,
            base,
            bytes,
            wide,
        } => Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: Pointer {
                block: base.block.clone(),
                offset: rewrite_offset_term(&base.offset, left, right),
            },
            bytes: rewrite_term(bytes, left, right),
            wide: *wide,
        },
        Proposition::Equal(Term::Algebraic(goal_left), Term::Algebraic(goal_right)) => {
            let rewrite_term = |term: &MachineTerm| rewrite_term(term, left, right);
            let rewrite_pointer = |pointer: &Pointer| Pointer {
                block: pointer.block.clone(),
                offset: rewrite_offset_term(&pointer.offset, left, right),
            };
            let rewrite_shared =
                |value: &SharedMachineIntegerTerm| rewrite_pointer_index(value, left, right);
            Proposition::Equal(
                Term::Algebraic(rewrite_algebraic(
                    goal_left,
                    &rewrite_term,
                    &rewrite_pointer,
                    &rewrite_shared,
                )),
                Term::Algebraic(rewrite_algebraic(
                    goal_right,
                    &rewrite_term,
                    &rewrite_pointer,
                    &rewrite_shared,
                )),
            )
        }
        _ => {
            return Err(AtomicRewriteRefusal::Absent(
                "`rewrite` int32 equality does not occur in this goal".to_string(),
            ));
        }
    };
    if &rewritten == goal {
        return Err(AtomicRewriteRefusal::Absent(
            "`rewrite` equality does not occur in the current goal".to_string(),
        ));
    }
    Ok(rewritten)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn checked_pointer_index_rewrite_preserves_shared_arithmetic() {
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            let _session = VerificationSession::enter();
            let x = MachineTerm::Variable(Variable(1081001));
            let y = MachineTerm::Variable(Variable(1081002));
            let root = KernelTerm::retained_machine_operand(ty, MachineOperandView::Legacy(&x));
            let root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
            let index = SharedMachineIntegerTerm::from_shared(ty, root).unwrap();
            let pointer = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: if ty == MachineIntegerType::Int32 {
                    PointerOffsetTerm::Int32Scaled {
                        value: index.clone(),
                        byte_width: 4,
                    }
                } else {
                    PointerOffsetTerm::Int64Scaled {
                        value: index.clone(),
                        byte_width: 4,
                        unsigned: ty == MachineIntegerType::UInt64,
                    }
                },
            };
            let goal = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(pointer.clone(), Pointer::symbolic(Variable(1081003))),
                true,
            );
            let equality = Proposition::ConditionIs(
                ConditionTerm::machine_compare(ty, CompareRelation::Equal, x.clone(), y.clone()),
                true,
            );
            let facts = ProofFacts::default().with_fact(equality.clone());
            let exports = KernelTermExport::machine_export_count();
            let checked = facts.check_equality_rewrite(&goal, &equality).unwrap();
            assert_ne!(checked.proposition(), &goal);
            assert!(
                ProofFacts::default()
                    .check_equality_rewrite(&goal, &equality)
                    .is_err()
            );
            let substituted = crate::kernel::reasoning::substitute_bitvector_variable_in_pointer(
                &pointer,
                Variable(1081001),
                &y,
            );
            assert_ne!(substituted, pointer);
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            assert!(!index.has_boxed_operand());
        }
    }

    #[test]
    fn address_rewrite_preserves_the_registered_read_width_without_prior_target_reads() {
        for bytes in [4, 8] {
            let _session = VerificationSession::enter();
            let memory = intern_memory(Memory::new());
            let index = MachineTerm::Variable(Variable(73_001));
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(73_002)), 4),
            };
            let address = base.offset_by_int32_elements(index.clone());
            crate::kernel::eval::record_load_access_width(memory.memory(), &address, bytes);
            let read = canonical_form_of_load(memory.clone(), address, LoadKind::Int32);
            let goal =
                Proposition::ConditionIs(ConditionTerm::signed_less_equal(read, 7u32.into()), true);
            let equality = Proposition::ConditionIs(ConditionTerm::equal(index, 0u32.into()), true);
            let rewritten = rewrite_with_admitted_equality(&goal, &equality).unwrap();
            let Proposition::ConditionIs(ConditionTerm::Compare { left, .. }, true) = rewritten
            else {
                panic!("rewritten scalar comparison");
            };
            assert!(matches!(*left, MachineTerm::MemoryLoad(..)));
            let observed = crate::kernel::eval::scalar_read_observation(
                crate::kernel::MachineOperandView::Legacy(&left),
            )
            .unwrap();
            assert_eq!(observed.bytes, bytes);
            assert_eq!(observed.pointer, base);
        }
    }

    #[test]
    fn address_rewrite_reaches_legacy_pointer_reads_beyond_eight_levels() {
        let _session = VerificationSession::enter();
        let memory = crate::kernel::intern_memory(Memory::new());
        let from = Pointer::symbolic(Variable(998_930));
        let to = Pointer::symbolic(Variable(998_931));
        let other = from.clone();
        let rewritten_other = to.clone();
        let cited =
            Proposition::ConditionIs(ConditionTerm::pointer_equal(from.clone(), to.clone()), true);
        let facts = ProofFacts::default().with_fact(cited.clone());
        let read = |address: &Pointer| {
            Pointer::symbolic(crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                address,
                LoadKind::Int32,
                4,
            ))
        };
        let mut input = from;
        let mut expected = to;
        for depth in 1..=32 {
            input = read(&input);
            expected = read(&expected);
            let goal = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(input.clone(), other.clone()),
                true,
            );
            let result = facts.check_equality_rewrite(&goal, &cited).unwrap();
            let wanted = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(expected.clone(), rewritten_other.clone()),
                true,
            );
            assert_eq!(result.proposition(), &wanted, "read depth {depth}");
        }
    }

    #[test]
    fn address_rewrite_preserves_native_read_versions_beside_a_shallow_occurrence() {
        let _session = VerificationSession::enter();
        let from = Pointer::symbolic(Variable(998_940));
        let to = Pointer::symbolic(Variable(998_941));
        let stored = ProgramValue::pointer(Pointer::symbolic(Variable(998_942)));
        let memory = Memory::new().store(to.clone(), stored);
        let memory = crate::kernel::intern_memory(memory);
        let cited =
            Proposition::ConditionIs(ConditionTerm::pointer_equal(from.clone(), to.clone()), true);
        let facts = ProofFacts::default().with_fact(cited.clone());
        let mut input = from.clone();
        let mut expected = to.clone();
        for depth in 1..=32 {
            input = Pointer::version_read(&memory, &input);
            expected = Pointer::version_read(&memory, &expected);
            let goal = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(input.clone(), from.clone()),
                true,
            );
            let wanted = Proposition::ConditionIs(
                ConditionTerm::pointer_equal(expected.clone(), to.clone()),
                true,
            );
            assert_eq!(
                facts
                    .check_equality_rewrite(&goal, &cited)
                    .unwrap()
                    .proposition(),
                &wanted,
                "read depth {depth}"
            );
        }
        let later = memory.memory().clone().store(
            to.clone(),
            ProgramValue::pointer(Pointer::symbolic(Variable(998_943))),
        );
        let _ = later.symbolic_pointer_version_load(&to, ProgramType::Int32Pointer);
        let goal = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(input.offset_by_bytes(8), from.clone()),
            true,
        );
        let wanted = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(expected.offset_by_bytes(8), to.clone()),
            true,
        );
        assert_eq!(
            facts
                .check_equality_rewrite(&goal, &cited)
                .unwrap()
                .proposition(),
            &wanted,
            "the displaced read retains the original state"
        );
    }

    #[test]
    fn address_rewrite_keeps_legacy_reads_named_when_the_target_stores_bits() {
        let _session = VerificationSession::enter();
        let from = Pointer::symbolic(Variable(998_960));
        let to = Pointer::symbolic(Variable(998_961));
        let memory = crate::kernel::intern_memory(
            Memory::new().store(to.clone(), ProgramValue::Int32(7u32.into())),
        );
        let read = |address: &Pointer| {
            let load =
                MachineTerm::MemoryLoad(memory.clone(), Box::new(address.clone()), LoadKind::Int32);
            let (variable, _) =
                crate::kernel::load_variable_for_term(&load).expect("legacy read adapter");
            Pointer::symbolic(variable)
        };
        let input = read(&from);
        let expected = read(&to);
        let cited =
            Proposition::ConditionIs(ConditionTerm::pointer_equal(from.clone(), to.clone()), true);
        let facts = ProofFacts::default().with_fact(cited.clone());
        let goal = Proposition::ConditionIs(ConditionTerm::pointer_equal(input, from), true);
        let wanted = Proposition::ConditionIs(ConditionTerm::pointer_equal(expected, to), true);
        assert_eq!(
            facts
                .check_equality_rewrite(&goal, &cited)
                .unwrap()
                .proposition(),
            &wanted
        );
    }

    fn observed_native_bound(ty: MachineIntegerType) -> MachineTerm {
        match ty {
            MachineIntegerType::Int64 => MachineTerm::int64_constant(10),
            MachineIntegerType::UInt64 => MachineTerm::uint64_constant(10),
            _ => MachineTerm::constant(10),
        }
    }

    fn observed_native_condition(
        ty: MachineIntegerType,
        operation: usize,
        left: MachineTerm,
        right: MachineTerm,
    ) -> ConditionTerm {
        use MachineIntegerType::{Int32, Int64, UInt32, UInt64};
        match (ty, operation) {
            (Int32 | UInt32, 0) => ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
            (Int64 | UInt64, 0) => ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
            (Int32, 1) => ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
            (Int64, 1) => ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
            (UInt32, 1) => ConditionTerm::unsigned_less_equal(left, right),
            (UInt64, 1) => ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: Box::new(left),
                right: Box::new(right),
            },
            (Int32, 2) => ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
            (Int64, 2) => ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
            (UInt32, 2) => ConditionTerm::unsigned_less_than(left, right),
            (UInt64, 2) => ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: Box::new(left),
                right: Box::new(right),
            },
            _ => unreachable!(),
        }
    }

    #[test]
    fn integer_rewrite_reaches_observations_beside_an_already_rewritten_integer_leaf() {
        use MachineIntegerType::{Int32, Int64, UInt32, UInt64};
        let word = MachineTerm::Variable(Variable(74_001));
        let target: SharedIntegerTerm = IntegerTerm::var(Variable(74_002)).into();
        let bound: SharedIntegerTerm = IntegerTerm::constant_i64(10).into();
        for ty in [Int32, UInt32, Int64, UInt64] {
            let source: SharedIntegerTerm =
                IntegerTerm::from_machine(ty, word.clone()).unwrap().into();
            let cited = Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(source.clone(), target.clone()),
                true,
            );
            let integer_leaf = Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(source.clone(), bound.clone()),
                true,
            );
            let expected_integer_leaf = Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(target.clone(), bound.clone()),
                true,
            );
            for operation in 0..3 {
                for reverse in [false, true] {
                    let (left, right, expected_left, expected_right) = if reverse {
                        (
                            observed_native_bound(ty),
                            word.clone(),
                            bound.clone(),
                            target.clone(),
                        )
                    } else {
                        (
                            word.clone(),
                            observed_native_bound(ty),
                            target.clone(),
                            bound.clone(),
                        )
                    };
                    for truth in [false, true] {
                        let native = Proposition::ConditionIs(
                            observed_native_condition(ty, operation, left.clone(), right.clone()),
                            truth,
                        );
                        let (condition, expected_truth) = match (operation, truth) {
                            (0, truth) => (
                                ConditionTerm::IntegerEqual(
                                    expected_left.clone(),
                                    expected_right.clone(),
                                ),
                                truth,
                            ),
                            (1, true) => (
                                ConditionTerm::IntegerLessEqual(
                                    expected_left.clone(),
                                    expected_right.clone(),
                                ),
                                true,
                            ),
                            (1, false) => (
                                ConditionTerm::IntegerLessThan(
                                    expected_right.clone(),
                                    expected_left.clone(),
                                ),
                                true,
                            ),
                            (2, true) => (
                                ConditionTerm::IntegerLessThan(
                                    expected_left.clone(),
                                    expected_right.clone(),
                                ),
                                true,
                            ),
                            (2, false) => (
                                ConditionTerm::IntegerLessEqual(
                                    expected_right.clone(),
                                    expected_left.clone(),
                                ),
                                true,
                            ),
                            _ => unreachable!(),
                        };
                        let goal =
                            Proposition::And(Box::new(integer_leaf.clone()), Box::new(native));
                        let expected = Proposition::And(
                            Box::new(expected_integer_leaf.clone()),
                            Box::new(Proposition::ConditionIs(condition, expected_truth)),
                        );
                        assert_eq!(
                            rewrite_with_admitted_equality(&goal, &cited).unwrap(),
                            expected,
                            "{ty:?} op {operation} reverse {reverse} truth {truth}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn integer_rewrite_keeps_other_observation_formats_and_operands_in_compounds() {
        use MachineIntegerType::{Int32, Int64, UInt32, UInt64};
        let word = MachineTerm::Variable(Variable(74_101));
        let target: SharedIntegerTerm = IntegerTerm::var(Variable(74_102)).into();
        let bound: SharedIntegerTerm = IntegerTerm::constant_i64(10).into();
        for source_ty in [Int32, UInt32, Int64, UInt64] {
            let source: SharedIntegerTerm = IntegerTerm::from_machine(source_ty, word.clone())
                .unwrap()
                .into();
            let cited = Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(source.clone(), target.clone()),
                true,
            );
            for goal_ty in [Int32, UInt32, Int64, UInt64] {
                if source_ty == goal_ty {
                    continue;
                }
                let native = Proposition::ConditionIs(
                    observed_native_condition(
                        goal_ty,
                        1,
                        word.clone(),
                        observed_native_bound(goal_ty),
                    ),
                    true,
                );
                let goal = Proposition::And(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::IntegerEqual(source.clone(), bound.clone()),
                        true,
                    )),
                    Box::new(native.clone()),
                );
                let expected = Proposition::And(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::IntegerEqual(target.clone(), bound.clone()),
                        true,
                    )),
                    Box::new(native),
                );
                assert_eq!(
                    rewrite_with_admitted_equality(&goal, &cited).unwrap(),
                    expected
                );
            }
            let native = Proposition::ConditionIs(
                observed_native_condition(
                    source_ty,
                    1,
                    MachineTerm::Variable(Variable(74_103)),
                    observed_native_bound(source_ty),
                ),
                true,
            );
            assert!(rewrite_with_admitted_equality(&native, &cited).is_err());
        }
    }

    #[test]
    fn integer_observation_rewrite_keeps_quantifier_capture_checks() {
        let variable = Variable(74_151);
        let word = MachineTerm::Variable(variable);
        let source = IntegerTerm::from_machine(MachineIntegerType::Int32, word.clone()).unwrap();
        let cited = integer_equality(source, IntegerTerm::var(Variable(74_152)));
        let goal = Proposition::ForAll {
            name: Default::default(),
            var: variable,
            sort: Sort::ProgramInt32,
            body: Box::new(Proposition::ConditionIs(
                observed_native_condition(
                    MachineIntegerType::Int32,
                    1,
                    word,
                    observed_native_bound(MachineIntegerType::Int32),
                ),
                true,
            )),
        };
        assert!(rewrite_with_admitted_equality(&goal, &cited).is_err());
    }

    #[test]
    fn modular_rewrite_substitutes_inside_a_signed_observation() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let i = MachineTerm::Variable(Variable(1007180));
        let count = MachineTerm::Variable(Variable(1007181));
        let start = MachineTerm::Variable(Variable(1007182));
        let observe = |value| IntegerTerm::from_machine(ty, value).unwrap();
        let cited = integer_equality(
            observe(i.clone()),
            IntegerTerm::add(observe(start.clone()), observe(count.clone())),
        );
        let goal = integer_equality(
            observe(MachineTerm::subtract(i, count)),
            observe(start.clone()),
        );
        let before = KernelTermExport::machine_export_count();
        let result = rewrite_with_admitted_equality(&goal, &cited).unwrap();
        assert_ne!(result, goal);
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    #[test]
    fn modular_rewrite_retains_shared_residue_operands() {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let x = KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1007190));
        let root = KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [x.clone(), x]);
        let observed = |format| {
            IntegerTerm::Machine(
                SharedMachineIntegerTerm::from_shared(
                    format,
                    root.with_machine_observation_type(format),
                )
                .unwrap(),
            )
        };
        let cited = integer_equality(observed(ty), IntegerTerm::constant_i64(-1));
        let goal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(
                observed(MachineIntegerType::UInt32),
                IntegerTerm::constant_i64(4294967295),
            ),
            true,
        );
        let before = KernelTermExport::machine_export_count();
        assert!(rewrite_with_admitted_equality_as_written(&goal, &cited).is_err());
        let rewritten = rewrite_with_admitted_equality(&goal, &cited).unwrap();
        assert_ne!(rewritten, goal);
        assert_eq!(KernelTermExport::machine_export_count(), before);
    }

    fn equality(left: MachineTerm, right: MachineTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(left),
                right: Box::new(right),
            },
            true,
        )
    }

    fn integer_equality(a: IntegerTerm, b: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(a.into(), b.into()), true)
    }

    /// `σ(x) == x` compares `x`'s bits with themselves (rule K6), at either
    /// orientation, and so does the residue of `to_integer(σ(x)) ==
    /// to_integer(x)`: rewriting by either leaves the goal as it is, so a
    /// rewrite search never stacks σ(σ(x)) or files `x` at `uint32`.
    #[test]
    fn a_sign_cast_equality_with_its_operand_is_a_vacuous_rewrite() {
        let x = MachineTerm::Variable(Variable(73_101));
        let tag = MachineTerm::Variable(Variable(73_102));
        let sigma_x = MachineTerm::sign_cast32(
            MachineIntegerType::Int32,
            MachineIntegerType::UInt32,
            x.clone(),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::unsigned_less_equal(
                MachineTerm::add_at(MachineIntegerType::UInt32, tag, sigma_x.clone()),
                MachineTerm::uint32_constant(2000),
            ),
            true,
        );
        let observed = |ty, term: &MachineTerm| {
            IntegerTerm::from_machine(ty, term.clone()).expect("a symbolic observation")
        };
        for equality in [
            Proposition::ConditionIs(
                ConditionTerm::uint32_equal(sigma_x.clone(), x.clone()),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::uint32_equal(x.clone(), sigma_x.clone()),
                true,
            ),
            equality(x.clone(), sigma_x.clone()),
            integer_equality(
                observed(MachineIntegerType::UInt32, &sigma_x),
                observed(MachineIntegerType::Int32, &x),
            ),
        ] {
            assert!(!equality_rewrite_applies(&goal, &equality), "{equality:?}");
            assert_eq!(
                rewrite_with_admitted_equality(&goal, &equality).ok(),
                Some(goal.clone()),
                "{equality:?}"
            );
        }
    }

    #[test]
    fn integer_rewrite_presentation_accepts_only_the_same_normalized_claim() {
        let index = MachineTerm::Variable(Variable(9901));
        let value = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            MachineTerm::Variable(Variable(9902)),
        )
        .unwrap();
        let other = IntegerTerm::from_machine(
            MachineIntegerType::UInt64,
            MachineTerm::Variable(Variable(9903)),
        )
        .unwrap();
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, index.clone()).unwrap();
        let rhs = IntegerTerm::add(
            IntegerTerm::constant_i64(1),
            IntegerTerm::multiply(IntegerTerm::constant_i64(255), observed),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(value.clone().into(), rhs.into()),
            true,
        );
        let cited = equality(index, MachineTerm::constant(16));
        let facts = ProofFacts::default().with_fact(cited.clone());
        let mut rewrite = facts.check_equality_rewrite(&goal, &cited).unwrap();
        let raw = rewrite.proposition().clone();
        let folded = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(
                value.clone().into(),
                IntegerTerm::constant_i64(4081).into(),
            ),
            true,
        );
        assert_ne!(
            raw, folded,
            "substitution retains constant-expression structure"
        );
        let wrong_bound = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(
                value.clone().into(),
                IntegerTerm::constant_i64(4082).into(),
            ),
            true,
        );
        let wrong_atom = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(other.into(), IntegerTerm::constant_i64(4081).into()),
            true,
        );
        let wrong_relation = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(value.into(), IntegerTerm::constant_i64(4081).into()),
            true,
        );
        for forged in [wrong_bound, wrong_atom, wrong_relation] {
            assert!(!rewrite.try_present_as(&forged));
            assert_eq!(rewrite.proposition(), &raw);
        }
        assert!(rewrite.try_present_as(&folded));
        assert_eq!(rewrite.proposition(), &folded);
    }

    #[test]
    fn native_equality_rewrite_retains_folded_literal_widening() {
        let source = MachineTerm::constant(u32::MAX);
        let replacement = MachineTerm::Variable(Variable(193_024));
        let value = MachineTerm::Variable(Variable(193_025));
        let cited = equality(source.clone(), replacement.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        for (folded, lifted) in [
            (
                MachineTerm::int64_constant(-1),
                MachineTerm::int64_from_32(replacement.clone()),
            ),
            (
                MachineTerm::int64_constant(i64::from(u32::MAX)),
                MachineTerm::int64_from_uint32(replacement.clone()),
            ),
            (
                MachineTerm::uint64_constant(u64::MAX),
                MachineTerm::uint64_from_int32(replacement.clone()),
            ),
            (
                MachineTerm::uint64_constant(u64::from(u32::MAX)),
                MachineTerm::uint64_from_32(replacement.clone()),
            ),
        ] {
            let condition = |bound| {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::UInt64,
                        relation: CompareRelation::LessThan,
                        left: Box::new(value.clone()),
                        right: Box::new(bound),
                    },
                    true,
                )
            };
            assert_eq!(
                facts
                    .check_equality_rewrite(&condition(folded), &cited)
                    .unwrap()
                    .proposition(),
                &condition(lifted)
            );
        }
        // These full-width values have the same low bits as the source, but
        // no matching widening of it. The equality grants no substitution.
        for bound in [
            MachineTerm::uint64_constant(0x1_ffff_ffff),
            MachineTerm::int64_constant(0x1_ffff_ffff),
            MachineTerm::int64_constant(-0x1_0000_0001),
        ] {
            let goal = Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::UInt64,
                    relation: CompareRelation::LessThan,
                    left: Box::new(value.clone()),
                    right: Box::new(bound),
                },
                true,
            );
            assert!(facts.check_equality_rewrite(&goal, &cited).is_err());
        }
    }

    #[test]
    fn native_equality_rewrite_recovers_unsigned_32_bit_order_bias() {
        let value = MachineTerm::Variable(Variable(193_026));
        let divisor = MachineTerm::Variable(Variable(193_027));
        for source in [65521, 0x8000_0001, u32::MAX] {
            let source = MachineTerm::constant(source);
            let cited = equality(source.clone(), divisor.clone());
            let facts = ProofFacts::default().with_fact(cited.clone());
            for make in [
                ConditionTerm::unsigned_less_than as fn(MachineTerm, MachineTerm) -> ConditionTerm,
                ConditionTerm::unsigned_less_equal,
            ] {
                for truth in [false, true] {
                    let condition = make(value.clone(), source.clone());
                    if matches!(condition, ConditionTerm::Constant(_)) {
                        continue; // A fully folded bound contains no operand to rewrite.
                    }
                    let goal = Proposition::ConditionIs(condition, truth);
                    let expected =
                        Proposition::ConditionIs(make(value.clone(), divisor.clone()), truth);
                    assert_eq!(
                        facts
                            .check_equality_rewrite(&goal, &cited)
                            .unwrap()
                            .proposition(),
                        &expected
                    );
                    assert!(
                        ProofFacts::default()
                            .check_equality_rewrite(&goal, &cited)
                            .is_err()
                    );
                }
            }
        }
    }

    #[test]
    fn native_read_rewrite_preserves_literal_guards_of_integer_claims() {
        let _session = crate::kernel::VerificationSession::enter();
        let read = MachineTerm::MemoryLoad(
            intern_memory(Memory::new()),
            Box::new(Pointer::symbolic(Variable(193_024))),
            LoadKind::Int32,
        );
        let replacement = MachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            MachineTerm::Variable(Variable(193_025)),
            MachineTerm::constant(1),
        );
        let cited = equality(read.clone(), replacement.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        for truth in [false, true] {
            let goal = |value| {
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::Constant(truth),
                        true,
                    )),
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::IntegerEqual(
                            IntegerTerm::from_machine(MachineIntegerType::Int32, value)
                                .unwrap()
                                .into(),
                            IntegerTerm::constant_i64(17).into(),
                        ),
                        true,
                    )),
                )
            };
            assert_eq!(
                facts
                    .check_equality_rewrite(&goal(read.clone()), &cited)
                    .unwrap()
                    .proposition(),
                &goal(replacement.clone())
            );
        }
        assert!(
            facts
                .check_equality_rewrite(
                    &Proposition::ConditionIs(ConditionTerm::Constant(true), true),
                    &cited,
                )
                .is_err()
        );
    }

    #[test]
    fn native_equality_rewrite_enters_integer_observation_bounds() {
        let x = MachineTerm::Variable(Variable(193_022));
        let y = MachineTerm::Variable(Variable(193_023));
        let cited = equality(x.clone(), y.clone());
        let observe = |value| IntegerTerm::from_machine(MachineIntegerType::UInt32, value).unwrap();
        let comparisons = [
            ConditionTerm::IntegerLessThan
                as fn(SharedIntegerTerm, SharedIntegerTerm) -> ConditionTerm,
            ConditionTerm::IntegerLessEqual,
            ConditionTerm::IntegerGreaterThan,
            ConditionTerm::IntegerGreaterEqual,
            ConditionTerm::IntegerNotEqual,
        ];
        for make in comparisons {
            let term =
                |value| IntegerTerm::add(observe(value), IntegerTerm::constant_i64(4294967295i64));
            for truth in [false, true] {
                let goal = Proposition::ConditionIs(
                    make(
                        term(x.clone()).into(),
                        IntegerTerm::constant_i64(8589934590i64).into(),
                    ),
                    truth,
                );
                let expected = Proposition::ConditionIs(
                    make(
                        term(y.clone()).into(),
                        IntegerTerm::constant_i64(8589934590i64).into(),
                    ),
                    truth,
                );
                let facts = ProofFacts::default().with_fact(cited.clone());
                assert_eq!(
                    facts
                        .check_equality_rewrite(&goal, &cited)
                        .unwrap()
                        .proposition(),
                    &expected
                );
                assert!(
                    ProofFacts::default()
                        .check_equality_rewrite(&goal, &cited)
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn integer_equality_rewrite_checks_exact_authority_direction_and_compound_terms() {
        let x = IntegerTerm::var(Variable(193_001));
        let y = IntegerTerm::var(Variable(193_002));
        let z = IntegerTerm::var(Variable(193_003));
        let source = IntegerTerm::truncating_quotient(x.clone(), z.clone());
        let cited = integer_equality(source.clone(), y.clone());
        let compound = |a| IntegerTerm::add(IntegerTerm::multiply(a, z.clone()), x.clone());
        let goal = integer_equality(compound(source.clone()), z.clone());
        let expected = integer_equality(compound(y.clone()), z.clone());
        let empty = ProofFacts::default();
        assert!(empty.check_equality_rewrite(&goal, &cited).is_err());
        for evidence in [cited.clone(), integer_equality(y.clone(), source.clone())] {
            let facts = empty.with_fact(evidence);
            let mut checked = facts.check_equality_rewrite(&goal, &cited).unwrap();
            assert_eq!(checked.proposition(), &expected);
            assert!(!checked.try_present_as(&integer_equality(compound(y.clone()), x.clone())));
            assert_eq!(checked.proposition(), &expected);
            let reverse = integer_equality(y.clone(), source.clone());
            assert_eq!(
                facts
                    .check_equality_rewrite(&expected, &reverse)
                    .unwrap()
                    .proposition(),
                &goal
            );
            assert!(
                facts
                    .check_equality_rewrite(&integer_equality(x.clone(), z.clone()), &cited)
                    .is_err()
            );
        }
        let false_cited = Proposition::Not(Box::new(cited.clone()));
        assert!(
            empty
                .with_fact(false_cited.clone())
                .check_equality_rewrite(&goal, &false_cited)
                .is_err()
        );
        let mut false_polarity = cited.clone();
        if let Proposition::ConditionIs(_, truth) = &mut false_polarity {
            *truth = false;
        }
        assert!(
            empty
                .with_fact(false_polarity.clone())
                .check_equality_rewrite(&goal, &false_polarity)
                .is_err()
        );
        assert_eq!(
            empty
                .check_equality_rewrite(&goal, &integer_equality(x.clone(), x.clone()))
                .unwrap()
                .proposition(),
            &goal
        );
        // Substitution preserves relation polarity rather than proving its result.
        let negative = Proposition::Not(Box::new(goal));
        assert_eq!(
            empty
                .with_fact(cited.clone())
                .check_equality_rewrite(&negative, &cited)
                .unwrap()
                .proposition(),
            &Proposition::Not(Box::new(expected))
        );
    }

    #[test]
    fn integer_equality_rewrite_preserves_scopes_and_machine_carriers() {
        let x = IntegerTerm::var(Variable(193_011));
        let y = IntegerTerm::var(Variable(193_012));
        let cited = integer_equality(x.clone(), y.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        let goal = integer_equality(IntegerTerm::multiply(x.clone(), x.clone()), y.clone());
        for variable in [Variable(193_011), Variable(193_012)] {
            let quantified = Proposition::ForAll {
                name: Default::default(),
                var: variable,
                sort: Sort::Integer,
                body: Box::new(goal.clone()),
            };
            assert!(facts.check_equality_rewrite(&quantified, &cited).is_err());
        }
        let unrelated = Proposition::ForAll {
            name: Default::default(),
            var: Variable(193_013),
            sort: Sort::Integer,
            body: Box::new(goal.clone()),
        };
        let expected = Proposition::ForAll {
            name: Default::default(),
            var: Variable(193_013),
            sort: Sort::Integer,
            body: Box::new(integer_equality(
                IntegerTerm::multiply(y.clone(), y.clone()),
                y.clone(),
            )),
        };
        assert_eq!(
            facts
                .check_equality_rewrite(&unrelated, &cited)
                .unwrap()
                .proposition(),
            &expected
        );
        let fold = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(2).into(),
            },
            IntegerTerm::constant_i64(0),
            Variable(193_012),
            Variable(193_014),
            x.clone(),
        );
        let refused =
            facts.check_equality_rewrite(&integer_equality(fold.clone(), y.clone()), &cited);
        assert!(
            refused
                .err()
                .unwrap()
                .contains("internal fold or match binder")
        );
        // A whole fold is still a valid exact occurrence: no binder is entered.
        let fold_cited = integer_equality(fold.clone(), y.clone());
        assert_eq!(
            facts
                .with_fact(fold_cited.clone())
                .check_equality_rewrite(&integer_equality(fold, x.clone()), &fold_cited)
                .unwrap()
                .proposition(),
            &integer_equality(y.clone(), x.clone())
        );
        for destination in [
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::Int128,
        ] {
            let cast = |value: IntegerTerm| {
                Term::Bitvector32(MachineTerm::IntegerToMachine {
                    value: value.into(),
                    destination,
                })
            };
            let native_goal = Proposition::Equal(cast(x.clone()), cast(y.clone()));
            assert_eq!(
                facts
                    .check_equality_rewrite(&native_goal, &cited)
                    .unwrap()
                    .proposition(),
                &Proposition::Equal(cast(y.clone()), cast(y.clone()))
            );
        }
        let application = |value: IntegerTerm| {
            IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "opaque_integer".into(),
                vec![PureFunctionArgument::Integer(value.into())],
            ))
        };
        let application_goal = integer_equality(application(x.clone()), y.clone());
        assert_eq!(
            facts
                .check_equality_rewrite(&application_goal, &cited)
                .unwrap()
                .proposition(),
            &integer_equality(application(y.clone()), y.clone())
        );
        let expanded = IntegerTerm::add(x.clone(), x.clone());
        let self_reference = integer_equality(x.clone(), expanded.clone());
        assert_eq!(
            facts
                .with_fact(self_reference.clone())
                .check_equality_rewrite(&integer_equality(x.clone(), y.clone()), &self_reference)
                .unwrap()
                .proposition(),
            &integer_equality(expanded, y.clone())
        );
        // One bitvector carrier can be observed at several widths and signs.
        // Equalities between its int64 observations grant no cross-type match.
        let observe =
            |ty| IntegerTerm::from_machine(ty, MachineTerm::Variable(Variable(193_015))).unwrap();
        let wide = integer_equality(observe(MachineIntegerType::Int64), y.clone());
        for ty in [
            MachineIntegerType::Int32,
            MachineIntegerType::UInt64,
            MachineIntegerType::Int128,
        ] {
            let wrong_carrier =
                integer_equality(IntegerTerm::multiply(observe(ty), x.clone()), y.clone());
            assert!(
                facts
                    .with_fact(wide.clone())
                    .check_equality_rewrite(&wrong_carrier, &wide)
                    .is_err()
            );
        }
    }

    #[test]
    fn integer_equality_rewrite_keeps_state_identity_and_checks_work_budget() {
        let _session = VerificationSession::enter();
        let pointer = Pointer {
            block: "integer-rewrite-retained_state".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = Memory::new().with_block("integer-rewrite-retained_state", 8);
        let after = before.clone().store(
            pointer.clone(),
            ProgramValue::Int64(MachineTerm::int64_constant(9)),
        );
        let observe = |memory: Memory| {
            IntegerTerm::from_machine(
                MachineIntegerType::Int64,
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(memory),
                    Box::new(pointer.clone()),
                    LoadKind::Bits64,
                ),
            )
            .unwrap()
        };
        let x = observe(before);
        let changed = observe(after);
        let y = IntegerTerm::var(Variable(193_031));
        let cited = integer_equality(x.clone(), y.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        let compound = |a| integer_equality(IntegerTerm::multiply(a, y.clone()), y.clone());
        assert!(
            facts
                .check_equality_rewrite(&compound(changed), &cited)
                .is_err()
        );
        assert_eq!(
            facts
                .check_equality_rewrite(&compound(x.clone()), &cited)
                .unwrap()
                .proposition(),
            &compound(y.clone())
        );
        let limits = crate::instrumentation::TacticWorkLimits {
            simple: 0,
            smart: 0,
            control: 0,
        };
        let result = crate::instrumentation::with_tactic_work_limits(limits, || {
            crate::instrumentation::collect(|| {
                let tactic = crate::instrumentation::TacticEvent {
                    source_tactic_path: None,
                    claim: "Integer equality rewrite".into(),
                    tactic_index: 0,
                    tactic_name: "rewrite".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                );
                let result = facts.check_equality_rewrite(&compound(x), &cited);
                crate::instrumentation::emit(
                    crate::instrumentation::VerificationEvent::TacticFailed(tactic),
                );
                result.err().unwrap()
            })
            .0
        });
        assert!(result.contains("work budget"), "{result}");
    }

    #[test]
    fn integer_equality_rewrite_preserves_unrelated_native_observation_syntax() {
        let x = IntegerTerm::var(Variable(193_041));
        let y = IntegerTerm::var(Variable(193_042));
        let cited = integer_equality(x.clone(), y.clone());
        let facts = ProofFacts::default().with_fact(cited.clone());
        // These raw native forms are valid opaque observation identities.
        // Congruence must not fold them while rewriting an unrelated Integer.
        let terms = [
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value: Box::new(MachineTerm::constant(1)),
                from: MachineIntegerType::Int32,
                to: MachineIntegerType::Int64,
            },
            MachineTerm::legacy_cast(
                MachineCastSpelling::Int64FromUInt32,
                Box::new(MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt32From64,
                    Box::new(MachineTerm::uint64_constant(1)),
                )),
            ),
            MachineTerm::If {
                condition: Box::new(ConditionTerm::Constant(true)),
                then_term: Box::new(MachineTerm::int64_constant(1)),
                else_term: Box::new(MachineTerm::int64_constant(2)),
            },
        ];
        for term in terms {
            let observed = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int64,
                MachineTerm::Binary {
                    format: MachineIntegerType::Int64,
                    op: MachineBinaryOp::Add,
                    left: Box::new(MachineTerm::Variable(Variable(193_043))),
                    right: Box::new(term),
                },
            ));
            let goal = integer_equality(observed.clone(), IntegerTerm::add(x.clone(), x.clone()));
            let expected =
                integer_equality(observed.clone(), IntegerTerm::add(y.clone(), y.clone()));
            assert_eq!(
                facts
                    .check_equality_rewrite(&goal, &cited)
                    .unwrap()
                    .proposition(),
                &expected
            );
            assert!(
                facts
                    .check_equality_rewrite(&integer_equality(observed.clone(), observed), &cited)
                    .is_err()
            );
        }
        // A payload that actually contains the cited Integer still rewrites,
        // while its surrounding native cast remains an exact cast node.
        let cast = |value: IntegerTerm| {
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int64,
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    value: Box::new(MachineTerm::IntegerToMachine {
                        value: value.into(),
                        destination: MachineIntegerType::Int32,
                    }),
                    from: MachineIntegerType::Int32,
                    to: MachineIntegerType::Int64,
                },
            ))
        };
        assert_eq!(
            facts
                .check_equality_rewrite(&integer_equality(cast(x), y.clone()), &cited)
                .unwrap()
                .proposition(),
            &integer_equality(cast(y.clone()), y)
        );
    }

    #[test]
    fn checked_rewrite_requires_the_cited_equality_in_its_own_context() {
        let x = MachineTerm::Variable(Variable(901));
        let y = MachineTerm::Variable(Variable(902));
        let one = MachineTerm::constant(1);
        let cited = equality(x.clone(), y.clone());
        let goal = equality(x.clone(), one.clone());
        let empty = ProofFacts::default();
        let established = empty.with_fact(cited.clone());
        let sibling = empty.with_fact(equality(y.clone(), one.clone()));
        assert!(empty.check_equality_rewrite(&goal, &cited).is_err());
        assert!(sibling.check_equality_rewrite(&goal, &cited).is_err());
        let result = established.check_equality_rewrite(&goal, &cited).unwrap();
        let (obligation, facts) = result.into_obligation((), None::<()>);
        assert_eq!(obligation.proposition(), &equality(y.clone(), one.clone()));
        assert!(facts.materialization_available(&cited));
        let reversed = ProofFacts::from_ordered(&[equality(y.clone(), x)]);
        let (obligation, _) = reversed
            .check_equality_rewrite(&goal, &cited)
            .unwrap()
            .into_obligation((), None::<()>);
        assert_eq!(obligation.proposition(), &equality(y, one));
    }

    #[test]
    fn checked_rewrite_rejects_forged_presentation_without_changing_result() {
        let x = MachineTerm::Variable(Variable(911));
        let y = MachineTerm::Variable(Variable(912));
        let cited = equality(x.clone(), y.clone());
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
        let goal = equality(x, MachineTerm::constant(3));
        let expected = equality(y, MachineTerm::constant(3));
        let mut result = facts.check_equality_rewrite(&goal, &cited).unwrap();
        let forged = equality(MachineTerm::constant(0), MachineTerm::constant(0));
        assert!(!result.try_present_as(&forged));
        assert!(result.try_present_as(&expected));
        let (obligation, retained) = result.into_obligation("display", None::<()>);
        assert_eq!(obligation.proposition(), &expected);
        assert!(retained.shares_premises_with(&facts));
    }

    // Both widths use the same corresponding-leaf checker. A write, a
    // different read kind, address, or operator cannot stand in for that leaf.
    #[test]
    fn compound_read_rewrite_checks_states_kinds_and_operators() {
        let _session = crate::kernel::VerificationSession::enter();
        for wide in [false, true] {
            let pointer = Pointer {
                block: "compound-rewrite".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let before = Memory::new().with_block("compound-rewrite", 16);
            let after = before.clone().with_block("local:compound-unrelated", 4);
            let changed = after.clone().store(
                pointer.clone(),
                if wide {
                    ProgramValue::UInt64(MachineTerm::uint64_constant(7))
                } else {
                    ProgramValue::Int32(MachineTerm::constant(7))
                },
            );
            let kind = if wide {
                LoadKind::Bits64
            } else {
                LoadKind::Int32
            };
            crate::kernel::eval::declare_load_access_width(&pointer, if wide { 8 } else { 4 });
            let load = |memory: &Memory, pointer: Pointer, kind| {
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory_ref(memory),
                    Box::new(pointer),
                    kind,
                )
            };
            let one = if wide {
                MachineTerm::uint64_constant(1)
            } else {
                MachineTerm::constant(1)
            };
            let mask = |value| {
                if wide {
                    MachineTerm::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::BitwiseAnd,
                        left: Box::new(value),
                        right: Box::new(one.clone()),
                    }
                } else {
                    binary_node!(Int32, BitwiseAnd, Box::new(value), Box::new(one.clone()))
                }
            };
            let eq = |a, b| {
                Proposition::ConditionIs(
                    if wide {
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left: Box::new(a),
                            right: Box::new(b),
                        }
                    } else {
                        ConditionTerm::equal(a, b)
                    },
                    true,
                )
            };
            let cited = eq(mask(load(&before, pointer.clone(), kind)), one.clone());
            let facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
            let goal = eq(mask(load(&after, pointer.clone(), kind)), one.clone());
            let checked = facts
                .check_equality_rewrite(&goal, &cited)
                .expect("unchanged selected cell");
            assert_eq!(
                checked.proposition(),
                &Proposition::ConditionIs(
                    if wide {
                        ConditionTerm::Compare {
                            format: MachineIntegerType::Int64,
                            relation: CompareRelation::Equal,
                            left: Box::new(one.clone()),
                            right: Box::new(one.clone()),
                        }
                    } else {
                        ConditionTerm::Constant(true)
                    },
                    true
                )
            );
            assert!(
                ProofFacts::default()
                    .check_equality_rewrite(&goal, &cited)
                    .is_err()
            );
            for wrong in [
                mask(load(&changed, pointer.clone(), kind)),
                mask(load(
                    &after,
                    pointer.clone(),
                    if wide {
                        LoadKind::Int32
                    } else {
                        LoadKind::Bits64
                    },
                )),
                mask(load(
                    &after,
                    Pointer {
                        offset: PointerOffsetTerm::Constant(8),
                        ..pointer.clone()
                    },
                    kind,
                )),
                if wide {
                    MachineTerm::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::BitwiseOr,
                        left: Box::new(load(&after, pointer.clone(), kind)),
                        right: Box::new(one.clone()),
                    }
                } else {
                    binary_node!(
                        Int32,
                        BitwiseOr,
                        Box::new(load(&after, pointer.clone(), kind)),
                        Box::new(one.clone()),
                    )
                },
            ] {
                assert!(
                    facts
                        .check_equality_rewrite(&eq(wrong, one.clone()), &cited)
                        .is_err()
                );
            }
        }
    }

    #[test]
    fn compound_read_rewrite_work_is_local_to_selected_expressions() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer {
            block: "compound-rewrite-work".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        crate::kernel::eval::declare_load_access_width(&pointer, 8);
        let before = Memory::new().with_block("compound-rewrite-work", 8);
        let after = before.clone().with_block("local:compound-rewrite-work", 4);
        let expression = |memory: &Memory, size| {
            let mut term = MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(memory),
                Box::new(pointer.clone()),
                LoadKind::Bits64,
            );
            for index in 0..size {
                term = MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::BitwiseXor,
                    left: Box::new(term),
                    right: Box::new(MachineTerm::Variable(Variable(931_000 + index))),
                };
            }
            term
        };
        let eq = |a, b| {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: Box::new(a),
                    right: Box::new(b),
                },
                true,
            )
        };
        let mut costs = Vec::new();
        for size in [8, 32, 128] {
            let cited = eq(expression(&before, size), MachineTerm::uint64_constant(1));
            let goal = eq(expression(&after, size), MachineTerm::uint64_constant(1));
            let mut context_costs = Vec::new();
            for ambient in [0, 32, 128] {
                let mut facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
                for i in 0..ambient {
                    facts = facts.with_fact(equality(
                        MachineTerm::Variable(Variable(930_000 + i)),
                        MachineTerm::constant(i as u32),
                    ));
                }
                crate::kernel::eval::clear_load_canonicalization_caches();
                let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                    facts.check_equality_rewrite(&goal, &cited)
                });
                assert!(result.is_ok());
                context_costs.push(work);
            }
            assert!(
                context_costs.iter().all(|work| *work <= context_costs[0]),
                "{context_costs:?}"
            );
            costs.push(context_costs[0]);
        }
        assert!(
            costs.windows(2).all(|pair| pair[1] <= 4 * pair[0]),
            "{costs:?}"
        );
    }

    #[test]
    fn checked_rewrite_presentation_requires_checked_load_transport() {
        let pointer = Pointer {
            block: "rewrite-presentation".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        // The load is an `int32` one. A stored value answers only for a read
        // of its own width, and a load whose width nobody recorded is taken
        // as the widest scalar access, which no `int32` store supplies.
        crate::kernel::eval::declare_load_access_width(&pointer, 4);
        let memory = Memory::new().with_block("rewrite-presentation", 4).store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(42)),
        );
        let changed = memory.clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(43)),
        );
        let load = |memory| {
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        let x = MachineTerm::Variable(Variable(931));
        let y = MachineTerm::Variable(Variable(932));
        let cited = equality(x.clone(), y.clone());
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&cited));
        let mut result = facts
            .check_equality_rewrite(&equality(x, load(memory)), &cited)
            .unwrap();
        assert!(!result.try_present_as(&equality(y.clone(), load(changed))));
        assert!(result.try_present_as(&equality(y.clone(), MachineTerm::constant(42))));
        let (obligation, _) = result.into_obligation((), None::<()>);
        assert_eq!(
            obligation.proposition(),
            &equality(y, MachineTerm::constant(42))
        );
    }

    #[test]
    fn equality_rewrite_does_not_capture_or_replace_a_quantifier_binder() {
        fn checked_rewrite(
            goal: &Proposition,
            equality: &Proposition,
            available: &[Proposition],
        ) -> Result<Proposition, String> {
            ProofFacts::from_ordered(available)
                .check_equality_rewrite(goal, equality)
                .map(|checked| checked.proposition)
        }
        let bound = Variable(2_000_000);
        let free = Variable(71);
        let atom = |left, right| {
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(left),
                    right: Box::new(right),
                },
                true,
            )
        };
        let variable = |id| MachineTerm::Variable(id);
        let quantified = |body| Proposition::ForAll {
            name: Default::default(),
            var: bound,
            sort: Sort::ProgramInt32,
            body: Box::new(body),
        };

        let shadowed = atom(variable(bound), MachineTerm::constant(0));
        let shadowed_goal = quantified(atom(variable(bound), MachineTerm::constant(0)));
        assert!(
            checked_rewrite(&shadowed_goal, &shadowed, std::slice::from_ref(&shadowed),).is_err(),
            "an outer equality cannot replace the bound occurrence"
        );

        let capturing = atom(variable(free), variable(bound));
        let capturing_goal = quantified(atom(variable(free), MachineTerm::constant(0)));
        assert!(
            checked_rewrite(
                &capturing_goal,
                &capturing,
                std::slice::from_ref(&capturing),
            )
            .is_err(),
            "the replacement's free variable cannot become bound"
        );
        let existential = Proposition::Exists {
            name: "witness".to_string(),
            var: bound,
            sort: Sort::ProgramInt32,
            body: Box::new(atom(variable(free), MachineTerm::constant(0))),
        };
        assert!(
            checked_rewrite(&existential, &capturing, std::slice::from_ref(&capturing),).is_err(),
            "existential binders obey the same capture rule"
        );

        let hidden_capture = atom(
            variable(free),
            MachineTerm::ClickFunctionApplication {
                name: "f".to_string(),
                arguments: vec![PureFunctionArgument::Value(ProgramValue::Int32(variable(
                    bound,
                )))],
            },
        );
        assert!(
            checked_rewrite(
                &capturing_goal,
                &hidden_capture,
                std::slice::from_ref(&hidden_capture),
            )
            .is_err(),
            "a variable inside a pure-function argument must not become bound"
        );

        let safe = atom(variable(free), MachineTerm::constant(0));
        assert_eq!(
            checked_rewrite(&capturing_goal, &safe, std::slice::from_ref(&safe),)
                .expect("an unrelated equality may still rewrite under the binder"),
            quantified(Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true
            )),
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/equality_rewrite/tests.rs");
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Both offset and scalar observation rewrites traverse native bounds
    // without changing their domain or replacing their high bits.
    #[test]
    fn wide_resource_bounds_survive_offset_and_scalar_rewriting() {
        let _session = crate::kernel::VerificationSession::enter();
        let offset =
            PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(984_700)), 4);
        let base = Pointer {
            block: crate::kernel::PointerBlock::Symbolic(Variable(984_701)),
            offset: offset.clone(),
        };
        let wide = MemoryRange::new_wide(
            base,
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1 << 33),
            4,
        );
        let goal = Proposition::ResourceContains {
            parent: Box::new(Resource::Memory(wide.clone())),
            child: Box::new(Resource::Memory(wide.clone())),
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(offset),
                Box::new(PointerOffsetTerm::Constant(0)),
            ),
            true,
        );
        let rewritten = rewrite_atomic_proposition_by_exact_equality(&goal, &equality).unwrap();
        let (_, range) = rewritten.memory_containment().unwrap();
        assert_eq!(range.kind(), crate::kernel::RangeIndexKind::UInt64);
        assert_eq!(range.bound_terms(), wide.bound_terms());
        let scalar_eq = Proposition::ConditionIs(
            ConditionTerm::equal(MachineTerm::Variable(Variable(984_700)), 0u32.into()),
            true,
        );
        let rewritten = rewrite_atomic_proposition_by_exact_equality(&goal, &scalar_eq).unwrap();
        let (_, range) = rewritten.memory_containment().unwrap();
        assert_eq!(range.kind(), wide.kind());
        assert_eq!(range.bound_terms(), wide.bound_terms());
        assert_eq!(range.base().offset.as_const(), Some(0));
    }
}

#[cfg(test)]
mod wide_bound_equality_reader_tests {
    use super::*;

    #[test]
    fn wide_range_bound_substitution_requires_full_width_equality() {
        let _session = crate::kernel::VerificationSession::enter();
        let end = MachineTerm::Variable(Variable(985_900));
        let wide = MemoryRange::new_wide(
            Pointer::symbolic(Variable(985_901)),
            MachineTerm::uint64_constant(0),
            end.clone(),
            1,
        );
        let goal = Proposition::ResourceContains {
            parent: Box::new(Resource::Memory(wide.clone())),
            child: Box::new(Resource::Memory(wide.clone())),
        };
        // Equality of a low word cannot turn a full native endpoint into zero.
        let narrow = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(end.clone()),
                right: Box::new(0u32.into()),
            },
            true,
        );
        assert!(rewrite_atomic_proposition_by_exact_equality(&goal, &narrow).is_err());
        let high = MachineTerm::uint64_constant(1 << 33);
        let full = Proposition::ConditionIs(ConditionTerm::uint64_equal(end, high.clone()), true);
        let rewritten = rewrite_atomic_proposition_by_exact_equality(&goal, &full).unwrap();
        let (_, range) = rewritten.memory_containment().unwrap();
        assert_eq!(range.kind(), wide.kind());
        assert_eq!(range.bound_terms().1, &high);
    }
}

#[cfg(test)]
mod numeric_address_annotation_tests {
    use super::*;

    fn check(p: Pointer, q: Pointer) {
        let class = crate::kernel::effective_type::CAccessClass::Struct(
            crate::kernel::effective_type::CStructClass::opaque("node"),
        );
        let observed = |pointer: &Pointer| {
            MachineTerm::object_pointer_address(pointer.clone(), Some(class.clone()))
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(observed(&p), observed(&q)),
            true,
        );
        let mask = |pointer: &Pointer| {
            Proposition::ConditionIs(
                ConditionTerm::uint64_equal(
                    MachineTerm::uint64_bitwise_and(
                        observed(pointer),
                        MachineTerm::uint64_constant(1),
                    ),
                    MachineTerm::uint64_constant(0),
                ),
                true,
            )
        };
        let goal = mask(&p);
        let expected = mask(&q);
        let facts = ProofFacts::from_ordered(std::slice::from_ref(&equality));
        let checked = facts.check_equality_rewrite(&goal, &equality).unwrap();
        assert_eq!(checked.proposition(), &expected);
        assert_eq!(
            rewrite_proposition_by_exact_equality(
                &goal,
                &equality,
                std::slice::from_ref(&equality)
            )
            .unwrap(),
            expected
        );
        let nested = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                observed(&p),
                MachineTerm::uint64_add(
                    observed(&q),
                    MachineTerm::uint64_bitwise_and(observed(&p), MachineTerm::uint64_constant(1)),
                ),
            ),
            true,
        );
        let masked = mask(&p);
        let mask_facts = ProofFacts::from_ordered(std::slice::from_ref(&masked));
        assert_eq!(
            mask_facts
                .check_equality_rewrite(&nested, &masked)
                .unwrap()
                .proposition(),
            &equality,
        );
        let left = PointerValue::new(p.clone(), ProgramType::Int32Pointer)
            .with_extent(Some(SubobjectExtent::constant(p, 4)));
        for width in [4, 8] {
            let right = PointerValue::new(q.clone(), ProgramType::Int32Pointer)
                .with_extent(Some(SubobjectExtent::constant(q.clone(), width)));
            assert!(
                !facts
                    .assumptions()
                    .pointer_designations_match(&left, &right)
            );
        }
    }
    #[test]
    fn address_equality_rewrites_canonical_alignment_masks_without_pointer_authority() {
        let _session = VerificationSession::enter();
        check(
            Pointer::symbolic(Variable(998_821)),
            Pointer::symbolic(Variable(998_822)),
        );
        check(
            Pointer::integer_address(MachineTerm::Variable(Variable(998_823))),
            Pointer::integer_address(MachineTerm::Variable(Variable(998_824))),
        );
    }
}
