//! A check that lowering is fact-stable.
//!
//! Facts may decide whether lowering succeeds, discharge its obligations,
//! and add side facts, but they never change the term it produces: when
//! lowering succeeds under facts and under no facts, the two terms are the
//! same up to the names of bound variables (`docs/internals/raise-lower-principle.md`).
//! A lowering that rewrites through a fact, such as `f(a)` to `g(b)` because
//! `f(a) == g(b)` is known, yields a term no other context lowers to, so the
//! fact holding it has no Surface form.
//!
//! Setting `CLICK_FACT_STABILITY=<path>` lowers every checked proof
//! proposition a second time with the same policy and no facts, and appends
//! one line per lowering whose fact-free result is not the same term: a
//! `differs` line when it is another term, `paths:N` when it is several
//! paths the facts chose among, and `refused` when it is refused. Only
//! `differs` breaks the current rule; the other two are where facts still
//! decide lowering instead of being obligations. The check only observes;
//! the lowering's own result is unchanged.

#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};

use super::Proposition;

thread_local! {
    /// Set while the fact-free lowering runs, so it is not checked in turn.
    static SHADOWING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
thread_local! {
    static CAPTURE: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `run` with the check recording to memory, and returns its lines.
#[cfg(test)]
pub(crate) fn capture(run: impl FnOnce()) -> Vec<String> {
    CAPTURE.with(|lines| lines.replace(Some(Vec::new())));
    run();
    CAPTURE.with(|lines| lines.take()).unwrap_or_default()
}

pub(crate) fn enabled() -> bool {
    if SHADOWING.with(std::cell::Cell::get) {
        return false;
    }
    #[cfg(test)]
    if CAPTURE.with(|lines| lines.borrow().is_some()) {
        return true;
    }
    crate::instrumentation::FACT_STABILITY_RECORDS.enabled()
}

/// The outcome of the fact-free lowering beside the lowering under facts.
pub(crate) enum FactFree {
    /// It produced this one term.
    Term(Proposition),
    /// It produced this many paths, not one: under facts, the facts chose.
    Paths(usize),
    /// It was refused: facts decided that the lowering succeeds.
    Refused,
}

/// Runs `lower` as the fact-free lowering.
pub(crate) fn shadow<T>(lower: impl FnOnce() -> T) -> T {
    struct Restore;
    impl Drop for Restore {
        fn drop(&mut self) {
            SHADOWING.with(|flag| flag.set(false));
        }
    }
    SHADOWING.with(|flag| flag.set(true));
    let _restore = Restore;
    crate::instrumentation::without_charging(lower)
}

/// Whether two lowered propositions are the same term up to the names of
/// bound variables, the equality both lowering audits use.
pub(crate) fn same_up_to_binders(left: &Proposition, right: &Proposition) -> bool {
    left == right
        || crate::kernel::api::contract_certification::propositions_alpha_equivalent(left, right)
        || (has_retained_machine_fold_comparison(left)
            && has_retained_machine_fold_comparison(right)
            && crate::kernel::proof::propositions_are_alpha_equal(left, right))
}

// The structural fold spelling introduces fresh binder IDs. Use the
// state-aware alpha key for the comparison, preserving free variables and
// the identity of any loads.
fn has_retained_machine_fold_comparison(proposition: &Proposition) -> bool {
    use crate::kernel::{IntegerTerm, integer_comparison_condition};
    let Some((integer_comparison_condition!(left, right), _)) = proposition.condition_native()
    else {
        return false;
    };
    [left, right].into_iter().any(|operand| {
        matches!(operand.as_ref(), IntegerTerm::Machine(machine)
            if machine.shared_operand().is_some_and(|root| root.has_machine_folds()))
    })
}

/// Records `site` when its lowering under facts differs from its fact-free
/// lowering.
pub(crate) fn compare(site: &str, with_facts: &Proposition, fact_free: &FactFree) {
    // Alpha comparison can rename binders and canonicalize read terms. Like
    // the shadow lowering, this is audit work, not work by the proof being
    // observed. Charging it makes enabling the audit change proof outcomes.
    crate::instrumentation::without_charging(|| compare_uncharged(site, with_facts, fact_free));
}

fn compare_uncharged(site: &str, with_facts: &Proposition, fact_free: &FactFree) {
    crate::instrumentation::FACT_STABILITY_RECORDS.count_checked();
    let line = match fact_free {
        FactFree::Term(term) if same_up_to_binders(with_facts, term) => {
            return;
        }
        // Facts decided whether the lowering succeeds. The current rule
        // admits this, but it is where definedness still lives inside
        // lowering rather than in an obligation, so the audit counts it.
        FactFree::Refused => format!(
            "refused\t{site}\t{}\t\t{}\n",
            bounded(with_facts),
            thread_name()
        ),
        FactFree::Term(term) => format!(
            "differs\t{site}\t{}\t{}\t{}\n",
            bounded(with_facts),
            bounded(term),
            thread_name()
        ),
        FactFree::Paths(count) => format!(
            "paths:{count}\t{site}\t{}\t\t{}\n",
            bounded(with_facts),
            thread_name()
        ),
    };
    #[cfg(test)]
    if CAPTURE.with(|lines| {
        lines
            .borrow_mut()
            .as_mut()
            .map(|lines| lines.push(line.clone()))
            .is_some()
    }) {
        return;
    }
    crate::instrumentation::FACT_STABILITY_RECORDS.write(&line);
}

/// The running thread's name, which names the mdtest fixture under
/// `scripts/audit.sh fact-stability`.
fn thread_name() -> String {
    std::thread::current().name().unwrap_or("").to_string()
}

fn bounded(proposition: &Proposition) -> String {
    format!("{proposition:?}")
        .chars()
        .filter(|c| *c != '\n' && *c != '\t')
        .take(4000)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ConditionTerm, MachineTerm, Variable};

    #[test]
    fn a_proposition_lowered_without_consulting_facts_is_stable() {
        let c = "int32 id(int32 x) { return x; }";
        let click = r#"verifying "f.c";

int32 id(int32 x) {
    requires 0 <= x and x <= 10;
    ensures result == x;
} by {
    have x <= 10;
    step_until(function.exit);
    close();
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c_sources(click, &[("f.c", c)]).unwrap();
        });
        assert!(lines.is_empty(), "{lines:#?}");
    }

    #[test]
    fn comparing_alpha_equivalent_binders_does_not_charge_the_observed_proof() {
        // The two differ in their display names only, so they are
        // alpha-equivalent but not one value, and comparing them is work.
        let quantified = |var: Variable, name: &str| {
            crate::kernel::quantifiers::test_exists(
                name.into(),
                var,
                crate::kernel::Sort::ProgramInt32,
                Proposition::MemoryLoadable {
                    memory: crate::kernel::SymbolicMemory::new().with_declared_scalar_block(
                        "local:word".into(),
                        4,
                        crate::kernel::ProgramType::Int32,
                    ),
                    base: crate::kernel::Address::symbolic(Variable(700)),
                    bytes: (MachineTerm::Variable(var)).into(),
                    wide: false,
                },
            )
        };
        let left = quantified(Variable(701), "x");
        let right = quantified(Variable(702), "y");
        let (equal, comparison_work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::api::contract_certification::propositions_alpha_equivalent(&left, &right)
        });
        assert!(equal);
        assert!(
            comparison_work > 0,
            "the regression must exercise real comparison work"
        );
        let (lines, audit_work) = crate::instrumentation::measure_deterministic_work(|| {
            capture(|| compare("binder budget", &left, &FactFree::Term(right)))
        });
        assert!(lines.is_empty());
        assert_eq!(audit_work, 0);
    }

    #[test]
    fn a_term_that_differs_from_its_fact_free_lowering_is_reported() {
        let decided = Proposition::condition_is(ConditionTerm::Constant(true), true);
        let written = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(7))),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        );
        let lines = capture(|| {
            compare("site", &decided, &FactFree::Term(written.clone()));
            compare("site", &written, &FactFree::Term(written.clone()));
            compare("site", &written, &FactFree::Refused);
            compare("site", &written, &FactFree::Paths(2));
        });
        assert_eq!(lines.len(), 3, "{lines:#?}");
        assert!(lines[0].starts_with("differs\tsite\t"), "{lines:#?}");
        assert!(lines[1].starts_with("refused\tsite\t"), "{lines:#?}");
        assert!(lines[2].starts_with("paths:2\tsite\t"), "{lines:#?}");
    }
}
