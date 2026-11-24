//! A test measurement of the facts a step's premise raising cannot spell.
//!
//! Every fact a proof state holds, and every goal it focuses, must have a
//! Surface form that lowers back to it: expansion writes the proof out as
//! steps a person could have written, so whatever those steps cite or prove
//! must be writable (`docs/internals/raise-lower-principle.md`). Under
//! [`capture`], each checked step records one line per fact it adds, and per
//! goal it leaves focused, saying whether premise raising (the route `solve`
//! takes, `ProofSearch::resolve_solve_premises`) spells it. Tests assert on
//! those lines. Over the corpus, `click audit raise-lower` measures the
//! canonical raiser instead.
//!
//! The census only observes: it never changes a proof, and outside a test
//! capture it is off.

#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{ConditionTerm, Proposition, Term};

#[cfg(test)]
thread_local! {
    /// The lines a test is capturing, in place of the file sink.
    static CAPTURE: std::cell::RefCell<Option<Vec<String>>> = const { std::cell::RefCell::new(None) };
}

/// Runs `run` with the census recording to memory, and returns its lines.
#[cfg(test)]
pub(crate) fn capture(run: impl FnOnce()) -> Vec<String> {
    CAPTURE.with(|lines| lines.replace(Some(Vec::new())));
    run();
    CAPTURE.with(|lines| lines.take()).unwrap_or_default()
}

pub(super) fn enabled() -> bool {
    #[cfg(test)]
    if CAPTURE.with(|lines| lines.borrow().is_some()) {
        return true;
    }
    false
}

/// What a censused proposition is, by its outermost kernel form. A quantifier
/// or implication is classified by the atom it finally concludes, since that
/// is what decides whether a Surface form exists.
pub(super) fn kind(proposition: &Proposition) -> String {
    match proposition {
        Proposition::ForAll { body, .. } => format!("forall/{}", kind(body)),
        Proposition::Exists { body, .. } => format!("exists/{}", kind(body)),
        Proposition::Implies(_, body) => format!("implies/{}", kind(body)),
        Proposition::And(left, _) => format!("and/{}", kind(left)),
        Proposition::Or(left, _) => format!("or/{}", kind(left)),
        Proposition::Not(body) => format!("not/{}", kind(body)),
        Proposition::SequenceMembership { .. } => "sequence-membership".into(),
        Proposition::Equal(left, _) => format!(
            "equal:{}",
            match left {
                Term::Bitvector32(_) => "bitvector",
                Term::Integer(_) => "integer",
                Term::Algebraic(_) => "algebraic",
                Term::Sequence(_) => "sequence",
                Term::ProgramValue(_) => "c-value",
                Term::PointerOffset(_) => "pointer-offset",
                Term::ArrayReadPoint(_) => "array-read-point",
                Term::ExecutionState(_) => "state",
                _ => "outcome",
            }
        ),
        Proposition::ConditionIs(condition, _) => {
            format!("condition:{}", condition_kind(condition.native_compat()))
        }
        Proposition::Predicate { name, .. } if name.starts_with("__click") => {
            "predicate:internal".into()
        }
        Proposition::Predicate { .. } => "predicate".into(),
        other => {
            let debug = format!("{other:?}");
            debug
                .split(|c: char| !c.is_alphanumeric())
                .next()
                .unwrap_or("other")
                .to_owned()
        }
    }
}

fn condition_kind(condition: &ConditionTerm) -> String {
    // A machine comparison or overflow test names its format and relation.
    if let Some((op, _, _)) = condition.as_bitvector_comparison() {
        let kind = if op.is_overflow() {
            "Overflows"
        } else {
            "Compare"
        };
        return format!("{kind}({} {})", op.format().name(), op.program_symbol());
    }
    let debug = format!("{condition:?}");
    debug
        .split(|c: char| !c.is_alphanumeric())
        .next()
        .unwrap_or("condition")
        .to_owned()
}

/// Appends one census line: `raised|unraised`, the role (`fact` or
/// `goal`), the kind, the claim, the tactic, the origin (`written` for a step
/// a person wrote, `smart` for one a smart tactic's search took, which matters
/// only if that search succeeds), and the diagnostic rendering.
pub(super) fn record(raised: bool, role: &str, kind: &str, claim: &str, tactic: &str, text: &str) {
    if !enabled() {
        return;
    }
    let text: String = text
        .chars()
        .map(|c| if c == '\n' || c == '\t' { ' ' } else { c })
        .take(300)
        .collect();
    let origin = if crate::instrumentation::smart_tactic_active() {
        "smart"
    } else {
        "written"
    };
    let line = format!(
        "{}\t{role}\t{kind}\t{claim}\t{tactic}\t{origin}\t{text}\n",
        if raised { "raised" } else { "unraised" }
    );
    #[cfg(test)]
    CAPTURE.with(|lines| {
        if let Some(lines) = lines.borrow_mut().as_mut() {
            lines.push(line);
        }
    });
    #[cfg(not(test))]
    let _ = line;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{MachineTerm, Sort, Variable};

    #[test]
    fn hidden_child_fields_have_structural_resource_surface_forms() {
        let fixture = crate::cli::parse_mdtest(
            std::path::Path::new("a_hidden_record_is_shown_beside_its_resource.md"),
            include_str!("../../../mdtests/a_hidden_record_is_shown_beside_its_resource.md"),
        )
        .unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let lines = capture(|| {
            let error = crate::surface::verify_c_sources(
                fixture.click_source.as_deref().unwrap(),
                &sources,
            )
            .unwrap_err();
            assert!(
                error.to_string().contains("`ensures result >= 1` failed"),
                "{error}"
            );
        });
        let fields = lines
            .iter()
            .filter(|line| {
                let parts = line.split('\t').collect::<Vec<_>>();
                parts.get(1) == Some(&"fact")
                    && parts.get(2) == Some(&"condition:Compare(int32 ==)")
                    && parts.get(4) == Some(&"unfold")
            })
            .collect::<Vec<_>>();
        assert!(!fields.is_empty(), "{lines:#?}");
        let rewrites = lines
            .iter()
            .filter(|line| {
                let parts = line.split('\t').collect::<Vec<_>>();
                parts.get(1) == Some(&"goal")
                    && parts.get(4) == Some(&"rewrite")
                    && parts.get(5) == Some(&"smart")
            })
            .collect::<Vec<_>>();
        assert!(!rewrites.is_empty(), "{lines:#?}");
        assert!(
            rewrites.iter().all(|line| line.starts_with("raised\t")),
            "{rewrites:#?}"
        );
        assert!(
            fields.iter().all(|line| line.starts_with("raised\t")),
            "{fields:#?}"
        );
    }

    #[test]
    fn joined_structural_read_goals_keep_a_raisable_memory_version() {
        let fixture =
            include_str!("../../../mdtests/a_join_forgets_a_cell_the_arms_disagree_on.md");
        let c = fixture
            .split("```c filename=")
            .nth(1)
            .unwrap()
            .split_once('\n')
            .unwrap()
            .1
            .split("```")
            .next()
            .unwrap();
        let click = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let click = click.replace(
            "    step();\n    close();",
            "    have p->left == p->left;\n    step();\n    close();",
        );
        let lines = capture(|| {
            let error = crate::surface::verify_c_sources(
                &click,
                &[("a_join_forgets_a_cell_the_arms_disagree_on.c", c)],
            )
            .unwrap_err();
            assert!(
                error.to_string().contains("`ensures result == 0` failed"),
                "{error}"
            );
        });
        let reads = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"goal")
                    && fields.get(2) == Some(&"condition:Compare(int32 ==)")
            })
            .collect::<Vec<_>>();
        assert!(!reads.is_empty(), "{lines:#?}");
        assert!(
            reads.iter().all(|line| line.starts_with("raised\t")),
            "{reads:#?}"
        );
    }

    #[test]
    fn reflexive_algebraic_comparisons_raise_the_same_after_lowering_and_rewrite() {
        let fixture = include_str!("../../../mdtests/reflexive_algebraic_comparisons.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        for (case, kind) in [
            ("equal", "equal:algebraic"),
            ("not_equal", "not/not/equal:algebraic"),
        ] {
            let written =
                format!("raised\tgoal\t{kind}\twritten_{case}.ensures_0\tintro()\twritten\t");
            let rewritten =
                format!("raised\tgoal\t{kind}\trewritten_{case}.ensures_0\trewrite\twritten\t");
            let raised = |prefix: &str| {
                lines
                    .iter()
                    .find_map(|line| line.strip_prefix(prefix))
                    .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
            };
            assert_eq!(raised(&written), raised(&rewritten));
        }
    }

    #[test]
    fn algebraic_match_reconstruction_raises_after_lowering_and_rewrite() {
        let fixture = include_str!("../../../mdtests/algebraic_match_reconstruction.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |prefix: &str| {
            lines
                .iter()
                .find_map(|line| line.strip_prefix(prefix))
                .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
        };
        assert_eq!(
            raised("raised\tgoal\tequal:algebraic\twritten.ensures_0\tintro()\twritten\t"),
            raised("raised\tgoal\tequal:algebraic\trewritten.ensures_0\trewrite\twritten\t"),
        );
        let error = crate::surface::verify_c_sources(
            "spec enum Pair { Both(int32, int32) }
             theorem swapped(p: Pair) {
                 ensures p == (match p { Pair::Both(a, b) => Pair::Both(b, a) }) by close();
             }",
            &[],
        )
        .unwrap_err();
        assert!(error.to_string().contains("known"), "{error}");
    }

    #[test]
    fn known_constructor_algebraic_match_raises_after_lowering_and_rewrite() {
        let fixture = include_str!("../../../mdtests/algebraic_match_on_known_constructor.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |prefix: &str| {
            lines
                .iter()
                .find_map(|line| line.strip_prefix(prefix))
                .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
        };
        let written =
            raised("raised\tgoal\tequal:algebraic\twritten.ensures_0\tintro()\twritten\t");
        let rewritten =
            raised("raised\tgoal\tequal:algebraic\trewritten.ensures_0\trewrite\twritten\t");
        assert!(written.contains("match Packet::Full(7)"), "{written}");
        assert_eq!(written, rewritten);
    }

    #[test]
    fn known_int32_match_keeps_the_same_comparison_after_rewrite() {
        let fixture = include_str!("../../../mdtests/int32_match_on_known_constructor.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |prefix: &str| {
            lines
                .iter()
                .find_map(|line| line.strip_prefix(prefix))
                .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
        };
        let written = raised(
            "raised\tgoal\tcondition:Compare(int32 ==)\twritten.ensures_0\tintro()\twritten\t",
        );
        let rewritten = raised(
            "raised\tgoal\tcondition:Compare(int32 ==)\trewritten.ensures_0\trewrite\twritten\t",
        );
        assert!(written.contains("match Packet::Full(7)"), "{written}");
        assert_eq!(written, rewritten);
    }

    #[test]
    fn reflexive_int32_matches_keep_both_comparison_operands() {
        for (scrutinee, parameters) in [("Packet::Full(7)", ""), ("p", "p: Packet")] {
            for (relation, prefix, suffix) in [("==", "", ""), ("!=", "not (", ")")] {
                let source = format!(
                    r#"
                    spec enum Packet {{ Empty, Full(int32) }}
                    theorem reflexive({parameters}) {{
                        ensures forall (unused: Integer) {{
                            {prefix}(match {scrutinee} {{ Packet::Empty => 0, Packet::Full(n) => n }})
                                {relation} (match {scrutinee} {{ Packet::Empty => 0, Packet::Full(n) => n }}){suffix}
                        }} by {{ intro(); normalize(); }}
                    }}
                    "#
                );
                let lines = capture(|| {
                    crate::surface::proof::without_implicit_solve(|| {
                        crate::surface::verify_click_theorems(&source).unwrap();
                    });
                });
                assert!(
                    lines.iter().any(|line| {
                        line.starts_with("raised\tgoal\tcondition:Compare(int32 ==)\treflexive.ensures_0\tintro()\t")
                            && line.matches(&format!("match {scrutinee}")).count() == 2
                    }),
                    "{lines:#?}"
                );
            }
        }
    }

    #[test]
    fn known_int32_matches_keep_order_after_lowering_and_rewrite() {
        let fixture = include_str!("../../../mdtests/int32_match_order_on_known_constructor.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |claim, tactic, operator| {
            let prefix = format!(
                "raised\tgoal\tcondition:Compare(int32 {operator})\t{claim}.ensures_0\t{tactic}\twritten\t"
            );
            lines
                .iter()
                .find_map(|line| line.strip_prefix(&prefix))
                .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
        };
        let written = raised("written", "intro()", "<");
        assert!(written.contains("match Packet::Full(-7)"), "{written}");
        assert_eq!(written, raised("rewritten", "rewrite", "<"));
        let right = raised("right_operand", "intro()", "<=");
        assert!(right.starts_with("0 <= match Packet::Empty"), "{right}");
        let both = raised("both_operands", "intro()", ">");
        assert_eq!(both.matches("match Packet::").count(), 2, "{both}");
        let non_strict = raised("non_strict", "intro()", ">=");
        assert!(
            non_strict.contains("match Packet::Full(-7)"),
            "{non_strict}"
        );

        let wrong = source.replacen("}) < 0", "}) > 0", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("`known` requires the current goal as an available semantic fact"),
            "{error}"
        );
    }

    #[test]
    fn known_integer_matches_keep_the_comparison_after_rewrite() {
        let fixture = include_str!("../../../mdtests/integer_match_on_known_constructor.md");
        let source = fixture
            .split("```")
            .nth(1)
            .unwrap()
            .strip_prefix("click\n")
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |claim: &str, tactic: &str, kind: &str| {
            let prefix =
                format!("raised\tgoal\tcondition:{kind}\t{claim}.ensures_0\t{tactic}\twritten\t");
            lines
                .iter()
                .find_map(|line| line.strip_prefix(&prefix))
                .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
        };
        for (name, datatype) in [("machine", "MachinePacket"), ("integer", "IntegerPacket")] {
            let written = raised(&format!("{name}_written"), "intro()", "IntegerEqual");
            let rewritten = raised(&format!("{name}_rewritten"), "rewrite", "IntegerEqual");
            assert!(
                written.contains(&format!("match {datatype}::Full(7)")),
                "{written}"
            );
            assert_eq!(written, rewritten);
        }
        assert!(
            raised("mixed_unselected", "intro()", "IntegerEqual")
                .contains("match MachinePacket::Empty")
        );
        assert!(
            raised("machine_disequal", "intro()", "IntegerNotEqual")
                .contains("match MachinePacket::Full(7)")
        );
        let wrong = source.replacen("}) == 8", "}) == 9", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("`known` requires the current goal as an available semantic fact"),
            "{error}"
        );
    }

    #[test]
    fn known_integer_matches_keep_order_after_lowering_and_rewrite() {
        let fixture = include_str!("../../../mdtests/integer_match_order_on_known_constructor.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |claim: &str, tactic: &str, kind: &str| {
            let prefix =
                format!("raised\tgoal\tcondition:{kind}\t{claim}.ensures_0\t{tactic}\twritten\t");
            lines
                .iter()
                .find_map(|line| line.strip_prefix(&prefix))
                .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
        };
        for (name, datatype) in [("machine", "MachinePacket"), ("integer", "IntegerPacket")] {
            let written = raised(&format!("{name}_written"), "intro()", "IntegerLessThan");
            let rewritten = raised(&format!("{name}_rewritten"), "rewrite", "IntegerLessThan");
            assert!(
                written.contains(&format!("match {datatype}::Full(7)")),
                "{written}"
            );
            assert_eq!(written, rewritten);
        }
        for (claim, kind) in [
            ("integer_written_le", "IntegerLessEqual"),
            ("integer_written_gt", "IntegerGreaterThan"),
            ("machine_empty_ge", "IntegerGreaterEqual"),
        ] {
            let goal = raised(claim, "intro()", kind);
            assert!(goal.contains("match "), "{goal}");
        }
        let wrong = source.replacen("}) < 9", "}) < 8", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("`known` requires the current goal as an available semantic fact"),
            "{error}"
        );
    }

    #[test]
    fn closed_integer_and_algebraic_comparisons_raise_both_arms() {
        let fixture = include_str!("../../../mdtests/closed_integer_and_algebraic_conditionals.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        for (claim, guard, then_arm, else_arm) in [
            ("integer_order", "1 < 2", "x", "y"),
            ("integer_equality", "false", "x", "y"),
            (
                "algebraic_equality",
                "1 == 2",
                "Choice::Left",
                "Choice::Right",
            ),
            ("algebraic_argument", "true", "a", "b"),
        ] {
            let marker = format!("\t{claim}.ensures_0\tintro()\twritten\t");
            let written = lines
                .iter()
                .filter(|line| line.starts_with("raised\tgoal\t"))
                .find_map(|line| line.split_once(&marker).map(|(_, written)| written))
                .unwrap_or_else(|| panic!("missing {marker:?}: {lines:#?}"));
            for part in [
                format!("if {guard}"),
                format!("{{ {then_arm} }}"),
                format!("{{ {else_arm} }}"),
            ] {
                assert!(written.contains(&part), "{written}");
            }
        }
        let wrong = source.replacen("}) == Choice::Right", "}) == Choice::Left", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("`known` requires the current goal as an available semantic fact"),
            "{error}"
        );
    }

    #[test]
    fn closed_word_equality_guards_keep_their_conditional() {
        let fixture = include_str!("../../../mdtests/closed_word_equality_conditionals.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        for (theorem, arms) in [
            ("signed_words", ["x", "y"]),
            ("unsigned_words", ["9u32", "3u32"]),
        ] {
            for index in 0..2 {
                let claim = format!("\t{theorem}.ensures_{index}\tintro()\twritten\t");
                let written = lines
                    .iter()
                    .filter(|line| line.starts_with("raised\tgoal\t"))
                    .find_map(|line| line.split_once(&claim).map(|(_, written)| written))
                    .unwrap_or_else(|| panic!("missing {claim:?}: {lines:#?}"));
                let (_, conditional) = written
                    .split_once("if ")
                    .unwrap_or_else(|| panic!("expected a conditional: {written}"));
                let (guard, _) = conditional.split_once(" {").unwrap();
                assert!(guard.contains(" == "), "{written}");
                for arm in arms {
                    assert!(conditional.contains(&format!("{{ {arm} }}")), "{written}");
                }
            }
        }
        let wrong = source.replacen("else { y }) == x", "else { y }) == y", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error.to_string().contains("goal did not normalize to true"),
            "{error}"
        );
    }

    #[test]
    fn closed_float_predicates_raise_with_their_arithmetic() {
        let fixture = include_str!("../../../mdtests/closed_float_arithmetic_keeps_operators.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        for (claim, operator) in [
            ("round_once_per_operation.ensures_0", " + "),
            ("round_once_per_operation.ensures_1", " - "),
            ("exceptional_results.ensures_0", " / "),
            ("exceptional_results.ensures_1", " / "),
        ] {
            let marker = format!("\t{claim}\tintro()\twritten\t");
            assert!(
                lines.iter().any(|line| line.starts_with("raised\tgoal\t")
                    && line
                        .split_once(&marker)
                        .is_some_and(|(_, written)| written.contains(operator))),
                "{claim}: {lines:#?}"
            );
        }
        let wrong = source.replacen("0x33800000u32", "0x34000000u32", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("`known` requires the current goal as an available semantic fact"),
            "{error}"
        );
    }

    #[test]
    fn simple_int32_range_folds_raise_bounds_seed_and_body() {
        let fixture =
            include_str!("../../../mdtests/pure_empty_int32_range_folds_keep_structure.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |claim: &str| {
            let marker = format!("\t{claim}.ensures_0\tintro()\twritten\t");
            lines
                .iter()
                .find_map(|line| {
                    line.strip_prefix("raised\tgoal\t")?
                        .split_once(&marker)
                        .map(|(_, written)| written.trim_end())
                })
                .unwrap_or_else(|| panic!("{claim}: {lines:#?}"))
        };
        for (claim, bounds, seed, body) in [
            ("literal_empty", "3..3", "5", "k"),
            ("symbolic_empty", "n..n", "5", "k"),
            ("descending_empty", "3..1", "5", "k"),
            ("symbolic_seed", "n..n", "seed", "acc + k"),
            ("longer_literal_nonempty", "1..4", "5", "k"),
            ("literal_body", "1..3", "5", "7"),
            ("accumulator_projection", "1..3", "seed", "acc"),
            ("symbolic_control", "lo..hi", "5", "k"),
        ] {
            let written = raised(claim);
            assert!(written.contains(bounds), "{written}");
            assert!(written.contains(&format!(".fold({seed},")), "{written}");
            assert!(written.contains(&format!("{{ {body} }}")), "{written}");
        }
        for (claim, wrong) in [("k }) == 5", "k }) == 6"), ("k }) == 3", "k }) == 4")] {
            let wrong = source.replacen(claim, wrong, 1);
            let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("`known` requires the current goal as an available semantic fact"),
                "{error}"
            );
        }
    }

    #[test]
    fn short_int32_range_fold_raises_before_computation() {
        let fixture =
            include_str!("../../../mdtests/pure_short_int32_range_folds_keep_structure.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        for (claim, expression) in [
            ("short_fold_seed", "(1..2).fold(seed, |acc, k| { acc })"),
            ("short_fold_sum", "(1..3).fold(5, |acc, k| { acc + k })"),
        ] {
            let marker = format!("\t{claim}.ensures_0\tintro()\twritten\t");
            assert!(
                lines.iter().any(|line| {
                    line.split_once(&marker)
                        .is_some_and(|(_, written)| written.contains(expression))
                }),
                "{claim}: {lines:#?}"
            );
        }

        let overflowing = r#"
            theorem overflow_in_second_step() {
                ensures (1..3).fold(2147483646, |acc: int32, k: int32| -> int32 { acc + k })
                    == -2147483647 by { normalize(); }
            }
        "#;
        let error = crate::surface::verify_c_sources(overflowing, &[]).unwrap_err();
        assert!(
            error.to_string().contains("not established: `false`"),
            "{error}"
        );
    }

    #[test]
    fn pure_sequence_membership_raises_after_intro_and_rewrite() {
        let fixture =
            include_str!("../../../mdtests/pure_sequence_membership_keeps_concatenation.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[])
                .map(|_| ())
                .unwrap()
        });
        for (claim, tactic, kind, written) in [
            (
                "membership_with_concat",
                "intro()",
                "sequence-membership",
                "a in [] ++ ([b] ++ [a])",
            ),
            ("singleton", "intro()", "sequence-membership", "a in [a]"),
            (
                "empty",
                "intro()",
                "not/sequence-membership",
                "not (a in [])",
            ),
            (
                "rewrite_membership",
                "rewrite",
                "sequence-membership",
                "b in [] ++ [b]",
            ),
        ] {
            let prefix = format!("raised\tgoal\t{kind}\t{claim}.ensures_0\t{tactic}\twritten\t");
            assert!(
                lines
                    .iter()
                    .any(|line| line.trim_end().strip_prefix(&prefix) == Some(written)),
                "{prefix:?}: {lines:#?}"
            );
        }
        let wrong = source.replacen("a in [a]", "a in []", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(error.to_string().contains("could not establish"), "{error}");
    }

    #[test]
    fn pure_sequence_comparison_raises_with_its_concatenation() {
        let fixture =
            include_str!("../../../mdtests/pure_sequence_equality_keeps_concatenation.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        let raised = |claim: &str, tactic: &str| {
            let prefix =
                format!("raised\tgoal\tequal:sequence\t{claim}.ensures_0\t{tactic}\twritten\t");
            lines
                .iter()
                .find_map(|line| line.strip_prefix(&prefix))
                .unwrap_or_else(|| panic!("missing {prefix:?}: {lines:#?}"))
        };
        assert!(
            raised("keeps_concatenation", "intro()").contains("[] ++ [a] ++ [b] == [a, b] ++ []")
        );
        assert!(raised("keeps_rewritten_concatenation", "rewrite").contains("[b] ++ [] == [b]"));

        let wrong = source.replacen("[a, b] ++ []", "[b, a] ++ []", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("`known` requires the current goal as an available semantic fact"),
            "{error}"
        );
    }

    #[test]
    fn pure_uint64_sequences_raise_after_intro_and_rewrite() {
        let fixture = include_str!("../../../mdtests/pure_uint64_sequences_keep_structure.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[]).unwrap();
        });
        for (claim, tactic, kind, written) in [
            (
                "wide_sequence_equality",
                "intro()",
                "equal:sequence",
                "[] ++ [a] ++ [b] == [a, b] ++ []",
            ),
            (
                "wide_literal_membership",
                "intro()",
                "sequence-membership",
                "18446744073709551615u64 in [] ++ [0u64, 18446744073709551615u64]",
            ),
            (
                "wide_empty_membership",
                "intro()",
                "not/sequence-membership",
                "not (a in [])",
            ),
            (
                "wide_rewritten_membership",
                "rewrite",
                "sequence-membership",
                "b in [] ++ [b]",
            ),
            (
                "wide_rewritten_equality",
                "rewrite",
                "equal:sequence",
                "[b] ++ [] == [b]",
            ),
        ] {
            let prefix = format!("raised\tgoal\t{kind}\t{claim}.ensures_0\t{tactic}\twritten\t");
            assert!(
                lines
                    .iter()
                    .any(|line| line.trim_end().strip_prefix(&prefix) == Some(written)),
                "{prefix:?}: {lines:#?}"
            );
        }
        let wrong = source.replacen("[a, b] ++ []", "[b, a] ++ []", 1);
        let error = crate::surface::verify_c_sources(&wrong, &[]).unwrap_err();
        assert!(
            error
                .to_string()
                .contains("`known` requires the current goal as an available semantic fact"),
            "{error}"
        );
    }

    #[test]
    fn algebraic_match_arm_values_name_unfold_facts() {
        let source = r#"
verifying "keep.c";
function is_cons(xs: List<int32>) -> Bool {
    match xs { List::Nil => false, List::Cons(value, tail) => true, }
}
resource modeled(p: int32*) { field items: List<int32>; owns *p; }
void keep(int32* p) {
    owns before: modeled(p);
} by {
    match before.items {
        List::Nil => { step_until(function.exit); close(); },
        List::Cons(value, tail_items) => {
            unfold(is_cons(List::Cons(value, tail_items)));
            step_until(function.exit);
            close();
        },
    }
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c_sources(source, &[("keep.c", "void keep(int32 *p) {}")])
                .unwrap();
        });
        let facts = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"fact")
                    && fields.get(2) == Some(&"condition:BoolApplication")
            })
            .collect::<Vec<_>>();
        assert!(!facts.is_empty(), "{lines:#?}");
        assert!(
            facts.iter().all(|line| line.starts_with("raised\t")),
            "{facts:#?}"
        );
    }

    fn check_algebraic_condition_fixture(fixture: &str) {
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_click_theorems(source).unwrap();
        });
        let equalities = lines
            .iter()
            .filter(|line| line.split('\t').nth(2) == Some("condition:BoolEqual"))
            .collect::<Vec<_>>();
        assert!(!equalities.is_empty(), "{lines:#?}");
        assert!(
            equalities.iter().all(|line| line.starts_with("raised\t")),
            "{equalities:#?}"
        );
    }

    #[test]
    fn nested_algebraic_conditions_in_list_facts_are_raised() {
        check_algebraic_condition_fixture(include_str!(
            "../../../mdtests/stdlib_list_compositionality.md"
        ));
    }

    #[test]
    fn rigid_algebraic_conditions_in_list_facts_are_raised() {
        // Exercise the generic proof itself: applications instantiate the
        // checked statement and no longer replay the library theorem's body.
        let library = include_str!("../../../library/list.click");
        let start = library.find("theorem contains_append<T>").unwrap();
        let rest = &library[start..];
        let end = rest[1..].find("\ntheorem ").map_or(rest.len(), |i| i + 1);
        let theorem =
            rest[..end].replace("theorem contains_append", "theorem rigid_contains_append");
        check_algebraic_condition_fixture(&format!("```click\n{theorem}\n```"));
    }

    #[test]
    fn generic_list_calls_keep_exact_surface_forms_after_unfold_and_intro() {
        for fixture in [
            include_str!("../../../mdtests/constructor_type_arguments_are_inferred.md"),
            include_str!(
                "../../../mdtests/a_proof_binder_has_its_type_for_constructor_inference.md"
            ),
        ] {
            let source = fixture
                .split("```click\n")
                .nth(1)
                .unwrap()
                .split("```")
                .next()
                .unwrap();
            let lines = capture(|| {
                crate::surface::verify_click_theorems(source).unwrap();
            });
            let facts = lines
                .iter()
                .filter(|line| line.split('\t').nth(1) == Some("fact"))
                .collect::<Vec<_>>();
            assert!(!facts.is_empty());
            assert!(
                facts.iter().all(|line| line.starts_with("raised\t")),
                "{facts:#?}"
            );
        }
    }

    #[test]
    fn generic_list_proof_expands_and_rechecks_without_implicit_search() {
        let source = r#"
import click::list;
theorem only_element(v: int32, x: int32) {
    requires list::contains(List<int32>::Cons(v, List<int32>::Nil), x);
    ensures v == x;
}
"#;
        let expanded = crate::surface::expansion::expand_c_claim_source_by_label(
            source,
            &[],
            "only_element.ensures_0",
        )
        .unwrap();
        crate::surface::proof::without_implicit_solve(|| {
            crate::surface::verify_click_theorems(&expanded).unwrap();
        });
    }

    #[test]
    fn boolean_function_unfold_facts_and_goals_have_exact_surface_forms() {
        let fixture = include_str!("../../../mdtests/a_bool_pure_function_states_a_claim.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let lines = capture(|| {
            crate::surface::verify_click_theorems(source).unwrap();
        });
        let bool_lines = lines
            .iter()
            .filter(|line| {
                line.split('\t')
                    .nth(2)
                    .is_some_and(|kind| kind.contains("Bool"))
            })
            .collect::<Vec<_>>();
        assert!(!bool_lines.is_empty(), "{lines:#?}");
        assert!(
            bool_lines.iter().all(|line| line.starts_with("raised\t")),
            "{bool_lines:#?}"
        );
    }

    #[test]
    fn boolean_function_proof_expands_and_rechecks_without_implicit_search() {
        let fixture = include_str!("../../../mdtests/a_bool_pure_function_states_a_claim.md");
        let source = fixture
            .split("```click\n")
            .nth(1)
            .unwrap()
            .split("```")
            .next()
            .unwrap();
        let expanded = crate::surface::expansion::expand_c_claim_source_by_label(
            source,
            &[],
            "chosen_positive.ensures_0",
        )
        .unwrap();
        crate::surface::proof::without_implicit_solve(|| {
            crate::surface::verify_click_theorems(&expanded).unwrap();
        });
    }

    #[test]
    fn introduced_narrow_binder_bounds_have_checked_surface_forms() {
        for ty in ["int8", "uint8", "int16", "uint16"] {
            let source = format!(
                r#"
                theorem bounded() {{
                    ensures forall (x: {ty}) {{ x == x }} by {{
                        let value = intro();
                        normalize();
                    }}
                }}
            "#
            );
            let lines = capture(|| {
                crate::surface::proof::without_implicit_solve(|| {
                    crate::surface::verify_click_theorems(&source).unwrap();
                });
            });
            // An 8- or 16-bit binder is a value of its own format, so its
            // range is the format's and intro states no bound fact; what the
            // census records is raised.
            let facts = lines
                .iter()
                .filter(|line| line.split('\t').nth(1) == Some("fact"))
                .collect::<Vec<_>>();
            assert!(facts.is_empty(), "{ty}: {facts:#?}");
            assert!(!lines.is_empty(), "{ty}");
            assert!(
                lines.iter().all(|line| line.starts_with("raised\t")),
                "{ty}: {lines:#?}"
            );
        }
    }

    #[test]
    fn an_obligation_probe_does_not_duplicate_the_unfold_census() {
        let source = r#"
            predicate positive(x: int32) { x > 0 }
            theorem from_positive(x: int32) {
                requires positive(x);
                ensures x > 0 by { unfold(positive(x)); close(); }
            }
        "#;
        let checked = capture(|| {
            crate::surface::proof::without_implicit_solve(|| {
                crate::surface::verify_click_theorems(source).unwrap();
            });
        });
        let probed = capture(|| {
            crate::surface::verify_click_theorems(source).unwrap();
        });
        assert!(
            checked
                .iter()
                .any(|line| line.split('\t').nth(4) == Some("unfold"))
        );
        assert_eq!(probed, checked, "probing is not another accepted operation");
    }

    /// After `a[i] = 5`, `a[i]` names the read at the store's version, so a
    /// rewrite that moves `a[j]` to `a[i]` leaves the goal `a[i] == 5`: the
    /// rewritten read is named as writing `a[i]` names it, not folded to the
    /// stored `5` (which would leave `true`, a goal no longer about `a`).
    #[test]
    fn a_rewrite_to_a_stored_cell_keeps_the_read_in_the_goal() {
        let c = "void set(int32* a, int32 i, int32 j) { a[i] = 5; }";
        let click = r#"verifying "set.c";
void set(int32* a, int32 i, int32 j) {
    requires 0 <= i and i < 4;
    requires i == j;
    owns a[0..4];
    ensures a[j] == 5;
} by {
    step_until(function.exit);
    close();
    rewrite(j, i);
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c_sources(click, &[("set.c", c)]).unwrap();
        });
        let rewritten = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"goal") && fields.get(4) == Some(&"rewrite")
            })
            .collect::<Vec<_>>();
        assert!(!rewritten.is_empty(), "{lines:#?}");
        assert!(
            rewritten.iter().all(
                |line| line.starts_with("raised\t") && line.trim_end().ends_with("\ta[i] == 5")
            ),
            "{rewritten:#?}"
        );
    }

    #[test]
    fn facts_an_unfold_adds_at_the_execution_frontier_are_raised() {
        let c = "struct cell { int32 value; int32 other; };\n\
                 void bump(struct cell* p) { int32 seen = p->other; p->value = seen; }";
        let click = r#"resource flat(p: struct cell*) {
    owns p->value;
    owns p->other;
}

verifying "f.c";

void bump(struct cell* p) {
    owns flat(p);
} by {
    step();
    unfold(flat(p));
    step_until(function.exit);
    fold(flat(p));
    close();
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c_sources(click, &[("f.c", c)]).unwrap();
        });
        let unfold_facts = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"fact") && fields.get(4) == Some(&"unfold")
            })
            .collect::<Vec<_>>();
        assert!(!unfold_facts.is_empty(), "{lines:#?}");
        assert!(
            unfold_facts.iter().all(|line| line.starts_with("raised\t")),
            "{unfold_facts:#?}"
        );
    }

    #[test]
    fn an_unfold_fact_over_a_match_arm_binder_is_raised_through_it() {
        let c = "struct node { uint64 tag; };\n\
                 void pack(struct node *p, struct node *id) { p->tag = 7; }";
        let click = r#"verifying "f.c";
spec enum Identity { At(struct node*) }
resource modeled(p: struct node*) {
    field model: Identity;
    match model { Identity::At(id) => { owns p->tag; fact p == id; }, }
}
resource tag_at(p: struct node*) { owns p->tag; }
void pack(struct node* p, struct node* id) {
    consumes before: modeled(p);
    ensures 1 == 1;
} by {
    match before.model { Identity::At(model_id) => {
        unfold(before);
        fold(tag_at(model_id));
        unfold(tag_at(model_id));
        step();
        fold(tag_at(model_id));
        step_until(function.exit); close();
    }, }
}
"#;
        let lines = capture(|| {
            crate::surface::verify_c_sources(click, &[("f.c", c)]).unwrap();
        });
        // The arm binder `model_id` names the only Surface form of this range.
        let binder_fact = lines
            .iter()
            .find(|line| line.ends_with("\tviewable((model_id as (uint8 *))[0..8])\n"))
            .unwrap_or_else(|| panic!("{lines:#?}"));
        assert!(binder_fact.starts_with("raised\t"), "{binder_fact}");
    }

    #[test]
    fn a_rewritten_goal_with_no_written_template_is_spelled() {
        // `unfold(Adds(&add3))` opens a contract's obligation, which no written
        // proposition spells; the goals the rewrites inside `solve` leave are
        // spelled from the kernel goal instead.
        let c = "int32 add3(int32 x) { return x + 3; }";
        let click = r#"verifying "f.c";

contract int32 Adds(int32 x) {
    let amount: int32;
    requires 0 <= x and x <= 1000;
    requires 0 <= amount and amount <= 1000;
    ensures result == x + amount;
}

int32 add3(int32 x) {
    requires 0 <= x and x <= 1000;
    ensures result == x + 3;
}

theorem add3_adds_four() {
    ensures Adds(&add3, { amount: 4 }) by {
        unfold(Adds(&add3, { amount: 4 }));
        close();
    }
}
"#;
        let lines = capture(|| {
            let _ = crate::surface::verify_c_sources(click, &[("f.c", c)]);
        });
        let rewritten_goals = lines
            .iter()
            .filter(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                fields.get(1) == Some(&"goal") && fields.get(4) == Some(&"rewrite")
            })
            .collect::<Vec<_>>();
        assert!(!rewritten_goals.is_empty(), "{lines:#?}");
        assert!(
            rewritten_goals
                .iter()
                .all(|line| line.starts_with("raised\t")),
            "{rewritten_goals:#?}"
        );
    }

    #[test]
    fn a_censused_fact_is_classified_by_the_atom_it_concludes() {
        let atom = Proposition::condition_is(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(Variable(1))),
                right: Box::new(MachineTerm::constant(0)),
            },
            true,
        );
        let guarded = crate::kernel::quantifiers::test_forall(
            Default::default(),
            Variable(1),
            Sort::ProgramInt32,
            Proposition::Implies(Box::new(atom.clone()), Box::new(atom.clone())),
        );
        assert_eq!(kind(&atom), "condition:Compare(int32 ==)");
        assert_eq!(kind(&guarded), "forall/implies/condition:Compare(int32 ==)");
        assert_eq!(
            kind(&Proposition::Predicate {
                name: "__click_internal".into(),
                arguments: Vec::new(),
            }),
            "predicate:internal"
        );
    }
}
