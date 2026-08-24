use super::*;

#[derive(Clone, Debug)]
struct ScalingSample {
    size: usize,
    work: usize,
    named_work: BTreeMap<String, usize>,
}

fn scaling_sample<R>(size: usize, operation: impl FnOnce() -> R) -> (R, ScalingSample) {
    let ((result, work), events) = crate::instrumentation::collect(|| {
        crate::instrumentation::measure_deterministic_work(operation)
    });
    let mut named_work = BTreeMap::<String, usize>::new();
    for event in events {
        let (name, work) = match event {
            crate::instrumentation::VerificationEvent::OperationFinished { name, work, .. } => {
                (format!("operation `{name}`"), work)
            }
            crate::instrumentation::VerificationEvent::TacticFinished { tactic, work, .. } => (
                format!("{} tactic `{}`", tactic.class, tactic.tactic_name),
                work,
            ),
            _ => continue,
        };
        *named_work.entry(name).or_default() += work;
    }
    (
        result,
        ScalingSample {
            size,
            work,
            named_work,
        },
    )
}

fn named_growth_diagnostic(samples: &[ScalingSample]) -> String {
    let mut names = BTreeSet::new();
    for sample in samples {
        names.extend(sample.named_work.keys().cloned());
    }
    let mut curves = names
        .into_iter()
        .map(|name| {
            let work = samples
                .iter()
                .map(|sample| sample.named_work.get(&name).copied().unwrap_or(0))
                .collect::<Vec<_>>();
            (work.last().copied().unwrap_or(0), name, work)
        })
        .filter(|(last, _, _)| *last != 0)
        .collect::<Vec<_>>();
    curves.sort_by(|left, right| right.0.cmp(&left.0).then_with(|| left.1.cmp(&right.1)));
    curves
        .into_iter()
        .take(8)
        .map(|(_, name, work)| format!("{name}: {work:?}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// Accepts the fixed-cost noise present in a complete verifier transaction
/// while rejecting a sustained quadratic curve. Four geometric sizes give
/// three adjacent ratios; requiring the two largest to stay below 3x catches
/// quadratic growth (4x per doubling) without encoding host timing.
fn near_linear_scaling(samples: &[ScalingSample]) -> bool {
    if samples.len() < 4 {
        return false;
    }
    for pair in samples.windows(2) {
        if pair[1].size != pair[0].size * 2 {
            return false;
        }
    }
    samples
        .windows(2)
        .skip(samples.len().saturating_sub(3))
        .all(|pair| pair[1].work <= pair[0].work.saturating_mul(3))
}

fn assert_near_linear_scaling(axis: &str, samples: &[ScalingSample]) {
    assert!(
        near_linear_scaling(samples),
        "{axis}: deterministic work grows faster than the simple-verification contract: {samples:?}; named work: {}",
        named_growth_diagnostic(samples),
    );
}

#[test]
fn bounded_statement_successor_exclusion_ignores_unrelated_ambient_facts() {
    let (replace_source, caller_source, base_click) =
        super::contract_tests::result_case_split_sources();
    let insertion = "                open(allocated_cell(owner)) {\n                }\n";
    let mut samples = Vec::new();
    let mut exclusion_work = Vec::new();
    for size in [8, 16, 32, 64] {
        let unrelated = (0..size)
            .map(|index| {
                format!(
                    "                have 0 <= {index} by {{\n                    normalize();\n                }}\n"
                )
            })
            .collect::<String>();
        let click_source = base_click.replacen(insertion, &format!("{insertion}{unrelated}"), 1);
        assert_ne!(
            click_source, base_click,
            "the ambient facts were not inserted"
        );
        let (verified, sample) = scaling_sample(size, || {
            verify_c0_sources(
                &click_source,
                &[
                    ("replace_allocated_cell.c", replace_source),
                    ("replace_then_branch.c", caller_source),
                ],
            )
        });
        verified.expect("the bounded successor product should ignore unrelated ambient facts");
        exclusion_work.push(
            sample
                .named_work
                .get("operation `bounded statement-successor exclusion`")
                .copied()
                .unwrap_or(0),
        );
        samples.push(sample);
    }
    assert!(
        exclusion_work.iter().all(|work| *work == exclusion_work[0]),
        "lane-exclusion work changed with unrelated ambient facts: {exclusion_work:?}"
    );
    assert_near_linear_scaling("bounded statement-successor ambient facts", &samples);
}

fn unrelated_identity_project(function_count: usize) -> (Vec<(String, String)>, String) {
    let mut c_sources = Vec::new();
    let mut click_source = String::new();
    for index in 0..function_count {
        let filename = format!("scaling_{index}.c");
        c_sources.push((
            filename.clone(),
            format!("int32 scaling_identity_{index}(int32 x) {{ return x; }}\n"),
        ));
        click_source.push_str(&format!("verifying \"{filename}\";\n"));
    }
    click_source.push('\n');
    for index in 0..function_count {
        click_source.push_str(&format!(
            "int32 scaling_identity_{index}(int32 x) {{\n    ensures result == x;\n}} by {{\n    step();\n    normalize();\n}}\n\n"
        ));
    }
    (c_sources, click_source)
}

fn target_with_unrelated_theorems(theorem_count: usize) -> String {
    let mut click_source = String::from("verifying \"target.c\";\n\n");
    for index in 0..theorem_count {
        click_source.push_str(&format!(
            "theorem unrelated_{index}(x: int32) {{\n    requires x == x;\n    ensures x == x by {{ assumption(); }}\n}}\n\n"
        ));
    }
    click_source.push_str(
        "int32 scaling_target(int32 x) {\n    ensures result == x;\n} by {\n    step();\n    normalize();\n}\n",
    );
    click_source
}

fn straight_line_project(statement_count: usize, snapshot_claim: bool) -> (String, String) {
    let mut c_source = String::from("int32 straight_line(int32 x) {\n");
    for _ in 0..statement_count {
        c_source.push_str("    x = x;\n");
    }
    c_source.push_str("    return x;\n}\n");

    let ensure = if snapshot_claim {
        "result == at(statement(0).entry, x)"
    } else {
        "result == x"
    };
    let mut click_source = format!(
        "verifying \"straight.c\";\n\nint32 straight_line(int32 x) {{\n    ensures {ensure};\n}} by {{\n"
    );
    for _ in 0..=statement_count {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    normalize();\n}\n");
    (c_source, click_source)
}

#[derive(Clone, Copy, Debug)]
enum LoadAxis {
    /// Each statement loads a new cell: one load variable each.
    DistinctCells,
    /// Every statement reloads `data[0]` from an unchanged memory.
    OneCell,
    /// Every statement reloads `data[0]` and stores `data[1]`: the reload
    /// finds its name again through a store DAG that grows with the proof.
    OneCellAcrossStores,
}

/// A straight line of loads from one array along one [`LoadAxis`].
/// Each statement is an explicit `step()`, so the certificate names each
/// load and the final claim compares the last local against the array cell
/// named at the function exit.
fn load_variable_project(statement_count: usize, axis: LoadAxis) -> (String, String) {
    let mut c_source =
        String::from("int32 load_line(int32 data[], int32 length) {\n    int32 x;\n");
    for index in 0..statement_count {
        match axis {
            LoadAxis::DistinctCells => c_source.push_str(&format!("    x = data[{index}];\n")),
            LoadAxis::OneCell => c_source.push_str("    x = data[0];\n"),
            LoadAxis::OneCellAcrossStores => {
                c_source.push_str("    x = data[0];\n    data[1] = x;\n");
            }
        }
    }
    c_source.push_str("    return x;\n}\n");
    let last = match axis {
        LoadAxis::DistinctCells => statement_count - 1,
        LoadAxis::OneCell | LoadAxis::OneCellAcrossStores => 0,
    };
    let (permission, statements) = match axis {
        LoadAxis::DistinctCells | LoadAxis::OneCell => ("views data[0..length];", statement_count),
        LoadAxis::OneCellAcrossStores => (
            "consumes data[0..length];\n    mutable data[1..2];\n    produces data[0..length];",
            2 * statement_count,
        ),
    };
    let mut click_source = format!(
        "verifying \"load_line.c\";\n\nint32 load_line(int32 data[], int32 length) {{\n    requires {statement_count} <= length;\n    requires 2 <= length;\n    {permission}\n    ensures result == data[{last}];\n}} by {{\n"
    );
    let statement_count = statements;
    for _ in 0..=statement_count + 1 {
        click_source.push_str("    step();\n");
    }
    click_source.push_str("    normalize();\n");
    if matches!(axis, LoadAxis::OneCellAcrossStores) {
        // `frame()` closes the effect claim; the `produces` claim has no
        // simple closer and takes the one smart tactic in this fixture.
        click_source.push_str("    frame();\n    simp();\n");
    }
    click_source.push_str("}\n");
    (c_source, click_source)
}

fn theorem_with_unrelated_exact_facts(fact_count: usize) -> String {
    let mut parameters = String::from("target: int32");
    let mut requirements = String::from("    requires target == 7;\n");
    for index in 0..fact_count {
        parameters.push_str(&format!(", unrelated_{index}: int32"));
        requirements.push_str(&format!(
            "    requires unrelated_{index} == {};\n",
            index as i32
        ));
    }
    format!(
        "theorem exact_fact_scaling({parameters}) {{\n{requirements}    ensures target == 7 by {{ assumption(); }}\n}}\n"
    )
}

/// A transitive order goal needs exactly two of its ambient conditions, so it
/// reaches the paired-candidate phase of condition-certificate search rather
/// than the single-candidate phase.
fn order_chain_theorem_with_unrelated_conditions(fact_count: usize) -> String {
    let mut parameters = String::from("low: int32, middle: int32, high: int32");
    let mut requirements =
        String::from("    requires low < middle;\n    requires middle < high;\n");
    for index in 0..fact_count {
        parameters.push_str(&format!(", unrelated_{index}: int32"));
        requirements.push_str(&format!(
            "    requires unrelated_{index} < {};\n",
            index as i32 + 1_000
        ));
    }
    format!(
        "theorem order_chain_scaling({parameters}) {{\n{requirements}    ensures low < high by {{ simp(); }}\n}}\n"
    )
}

fn function_with_unrelated_facts(fact_count: usize, proof: &str) -> (String, String) {
    let c_source = "int32 exact_fact_target(int32 target) { return target; }\n".to_string();
    let mut click_source = String::from(
        "verifying \"exact_fact_target.c\";\n\nint32 exact_fact_target(int32 target) {\n    requires target == 7;\n",
    );
    for index in 0..fact_count {
        click_source.push_str(&format!("    requires target != {};\n", index + 100));
    }
    click_source.push_str("    ensures result == 7;\n} by {\n");
    click_source.push_str(proof);
    click_source.push_str("}\n");
    (c_source, click_source)
}

fn theorem_with_many_forms(form_count: usize) -> String {
    let mut requirements = String::new();
    for zero_count in 0..form_count {
        let expression = format!("target{}", " + 0".repeat(zero_count));
        requirements.push_str(&format!("    requires {expression} == 7;\n"));
    }
    format!(
        "theorem surface_form_scaling(target: int32) {{\n{requirements}    ensures target == 7 by {{ assumption(); }}\n}}\n"
    )
}

fn grouped_claim_project(claim_count: usize) -> (String, String) {
    let c_source = "int32 shared_claims(int32 x) { return x; }\n".to_string();
    let mut click_source =
        String::from("verifying \"shared_claims.c\";\n\nint32 shared_claims(int32 x) {\n");
    for _ in 0..claim_count {
        click_source.push_str("    ensures result == x;\n");
    }
    click_source.push_str("} by {\n    step();\n    normalize();\n}\n");
    (c_source, click_source)
}

fn resource_member_project(member_count: usize) -> (String, String) {
    let c_source = "int32 preserve_bundle(int32 p[]) { return 0; }\n".to_string();
    let mut click_source = String::new();
    for index in 0..member_count {
        click_source.push_str(&format!(
            "abstract resource member_{index}(value: int32);\n"
        ));
    }
    click_source.push_str("\nresource bundle(p: int32*) {\n");
    for index in 0..member_count {
        click_source.push_str(&format!("    contains member_{index}({index});\n"));
    }
    click_source.push_str(
        "}\n\nverifying \"preserve_bundle.c\";\n\nint32 preserve_bundle(int32 p[]) {\n    views bundle(p);\n    immutable by {\n        step() using {}\n        frame() using {}\n    }\n}\n",
    );
    (c_source, click_source)
}

pub(super) fn theorem_with_parenthesized_requirement(depth: usize) -> String {
    let opening = "(".repeat(depth);
    let closing = ")".repeat(depth);
    format!(
        "theorem nested_requirement(x: int32) {{\n    requires {opening}x + 1{closing} == x + 1;\n    ensures x == x by {{ assumption(); }}\n}}\n"
    )
}

#[test]
fn parenthesized_contract_expression_parsing_has_linear_deterministic_work() {
    let samples = [2, 4, 8, 16]
        .into_iter()
        .map(|depth| {
            let source = theorem_with_parenthesized_requirement(depth);
            let (parsed, work) = crate::instrumentation::measure_deterministic_work(|| {
                parser::parse_file_items(&source)
            });
            parsed.unwrap_or_else(|error| {
                panic!(
                    "depth {depth} parenthesized requirement failed: {}",
                    error.message()
                )
            });
            ScalingSample {
                size: depth,
                work,
                named_work: BTreeMap::new(),
            }
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("parenthesized contract-expression parsing", &samples);
}

#[test]
fn simple_unrelated_functions_have_a_deterministic_scaling_control() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let (c_sources, click_source) = unrelated_identity_project(size);
            let source_refs = c_sources
                .iter()
                .map(|(name, source)| (name.as_str(), source.as_str()))
                .collect::<Vec<_>>();
            let (verified, sample) =
                scaling_sample(size, || verify_c0_sources(&click_source, &source_refs));
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} simple scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), size);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("unrelated simple functions", &samples);
}

#[test]
fn targeted_simple_verification_does_not_verify_unrelated_theorems() {
    let c_source = "int32 scaling_target(int32 x) { return x; }\n";
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let click_source = target_with_unrelated_theorems(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources_functions(
                    &click_source,
                    &[("target.c", c_source)],
                    ["scaling_target".to_string()],
                )
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} targeted scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), 1);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("target with unrelated theorems", &samples);
    assert!(
        samples.last().unwrap().work <= samples.first().unwrap().work.saturating_mul(2),
        "target work should be insensitive to unrelated theorems: {samples:?}"
    );
}

#[test]
fn targeted_certification_keeps_an_explicit_theorem_dependency() {
    let c_source = "int32 scaling_target(int32 x) { return x; }\n";
    let click_source = r#"
        theorem equality_symmetric(first: int32, second: int32) {
            requires first == second;
            ensures second == first by { simp(); }
        }

        verifying "target.c";
        int32 scaling_target(int32 x) {
            ensures x == result;
        } by {
            step();
            apply(equality_symmetric(result, x));
            assumption();
        }
    "#;
    verify_c0_sources_functions(
        click_source,
        &[("target.c", c_source)],
        ["scaling_target".to_string()],
    )
    .expect("targeted certification should retain its applied theorem closure");
}

#[test]
fn straight_line_simple_steps_scale_near_linearly_with_retained_snapshots() {
    for snapshot_claim in [false, true] {
        let samples = [8, 16, 32, 64]
            .into_iter()
            .map(|size| {
                let (c_source, click_source) = straight_line_project(size, snapshot_claim);
                let (verified, sample) = scaling_sample(size, || {
                    verify_c0_sources(&click_source, &[("straight.c", c_source.as_str())])
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "size {size} straight-line fixture (snapshot={snapshot_claim}) failed: {}",
                        error.message()
                    )
                });
                sample
            })
            .collect::<Vec<_>>();
        assert_near_linear_scaling("straight-line simple steps", &samples);
    }
}

/// Load variables are content-addressed: constructing one, and finding the
/// same variable again for an unwritten cell at a later point, must cost work
/// proportional to the load and the steps it crosses, not to the number of
/// load variables or facts already in the proof.
#[test]
fn load_variable_construction_scales_near_linearly_with_statements() {
    for axis in [
        LoadAxis::DistinctCells,
        LoadAxis::OneCell,
        LoadAxis::OneCellAcrossStores,
    ] {
        let samples = [8, 16, 32, 64]
            .into_iter()
            .map(|size| {
                let (c_source, click_source) = load_variable_project(size, axis);
                let (verified, sample) = scaling_sample(size, || {
                    verify_c0_sources(&click_source, &[("load_line.c", c_source.as_str())])
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "size {size} load-line fixture ({axis:?}) failed: {}",
                        error.message()
                    )
                });
                sample
            })
            .collect::<Vec<_>>();
        assert_near_linear_scaling(&format!("load-variable construction ({axis:?})"), &samples);
    }
}

#[test]
fn exact_assumption_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let source = theorem_with_unrelated_exact_facts(size);
            let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} exact-fact scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), 1);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("exact assumption with unrelated facts", &samples);
}

#[test]
fn transitive_order_derivation_scales_near_linearly_with_unrelated_conditions() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let source = order_chain_theorem_with_unrelated_conditions(size);
            let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} order-chain scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), 1);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("transitive order derivation", &samples);
}

#[test]
fn explicit_step_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = function_with_unrelated_facts(
                size,
                "    step() using {\n        target == 7;\n    }\n    assumption();\n",
            );
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("exact_fact_target.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit-step scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("explicit step with unrelated facts", &samples);
}

#[test]
fn explicit_transport_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = function_with_unrelated_facts(
                size,
                "    step() using {\n        target == 7;\n    }\n    transport(target == 7, result == 7) using {\n        target == 7;\n    }\n    assumption();\n",
            );
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(
                    &click_source,
                    &[("exact_fact_target.c", c_source.as_str())],
                )
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit-transport scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("explicit transport with unrelated facts", &samples);
}

#[test]
fn same_kernel_fact_with_many_surface_forms_scales_near_linearly() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let source = theorem_with_many_forms(size);
            let (verified, sample) = scaling_sample(size, || verify_click_theorems(&source));
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} surface-form scaling fixture failed: {}",
                    error.message()
                )
            });
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("same kernel fact with many surface forms", &samples);
}

#[test]
fn grouped_claims_share_one_execution_with_near_linear_work() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = grouped_claim_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("shared_claims.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} shared-claim scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), size);
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("claims sharing one execution", &samples);
}

#[test]
fn composite_definition_members_scale_near_linearly() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = resource_member_project(size);
            let (verified, sample) = scaling_sample(size, || {
                verify_c0_sources(&click_source, &[("preserve_bundle.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} resource-member scaling fixture failed: {}",
                    error.message()
                )
            });
            assert!(!verified.is_empty());
            sample
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("composite definition members", &samples);
}

/// The issue-named condition-derivation curve: one two-premise order
/// derivation while unrelated condition facts grow. The premise search must
/// not rerun the prover once per candidate pair.
#[test]
fn condition_derivation_scales_near_linearly_with_unrelated_conditions() {
    use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition, Variable};

    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let x = Bitvector32Term::Variable(Variable(430_000));
            let y = Bitvector32Term::Variable(Variable(430_001));
            let z = Bitvector32Term::Variable(Variable(430_002));
            let mut available = Vec::new();
            for index in 0..size {
                available.push(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(Bitvector32Term::Variable(Variable(431_000 + index as u64))),
                        Box::new(Bitvector32Term::Constant(1_000 + index as u32)),
                    ),
                    true,
                ));
            }
            available.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(x.clone()), Box::new(y.clone())),
                true,
            ));
            available.push(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(y), Box::new(z.clone())),
                true,
            ));
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(x), Box::new(z)),
                true,
            );
            let (derivation, work) = crate::instrumentation::measure_deterministic_work(|| {
                search_condition_derivation(&goal, &available)
            });
            let derivation = derivation
                .unwrap_or_else(|error| panic!("size {size} search failed: {}", error.message()))
                .expect("the chained order facts derive the goal");
            assert!(
                !derivation.context_premises().is_empty(),
                "the derivation should name its premises"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "condition derivation search is superlinear: {samples:?}"
        );
    }
}

#[test]
fn scaling_assertion_rejects_a_quadratic_curve() {
    let quadratic = [16, 32, 64, 128]
        .into_iter()
        .map(|size| ScalingSample {
            size,
            work: size * size,
            named_work: BTreeMap::from([(
                "operation `quadratic reference`".to_string(),
                size * size,
            )]),
        })
        .collect::<Vec<_>>();
    assert!(!near_linear_scaling(&quadratic));
    assert!(named_growth_diagnostic(&quadratic).contains("quadratic reference"));
}

#[test]
fn program_point_branch_merge_visits_only_fork_local_changes() {
    let point = |name: String| ProgramPointRef {
        region: CodeRegionRef::Mark(name),
        kind: ProgramPointKind::Entry,
    };
    let common_point = point("common".to_string());
    let left_only = point("left-only".to_string());
    let right_only = point("right-only".to_string());
    let common_state = CState::new();
    let mut samples = Vec::new();

    for size in [16_usize, 64, 256, 1024, 4096] {
        let mut ancestor = ProgramPointStates::new();
        for index in 0..size {
            ancestor.insert(point(format!("ambient-{index:05}")), CState::new());
        }
        let mut left = ancestor.clone();
        let mut right = ancestor.clone();
        left.insert(common_point.clone(), common_state.clone());
        right.insert(common_point.clone(), common_state.clone());
        left.insert(left_only.clone(), CState::new());
        right.insert(right_only.clone(), CState::new());

        let before = program_point_node_allocations();
        let merged = left
            .common_descendant(&right, &ancestor)
            .expect("fork siblings should have an exact persistent ancestor");
        let allocations = program_point_node_allocations() - before;
        samples.push((
            size,
            (usize::BITS - size.leading_zeros()) as usize,
            allocations,
        ));

        assert_eq!(merged.get(&common_point), Some(&common_state));
        assert!(merged.get(&left_only).is_none());
        assert!(merged.get(&right_only).is_none());
        assert_eq!(
            merged.get(&point(format!("ambient-{:05}", size / 2))),
            Some(&CState::new())
        );
        assert_eq!(ancestor.iter().count(), size);

        let unrelated = ProgramPointStates::new();
        assert!(left.common_descendant(&right, &unrelated).is_none());
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 8 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} program-point merge allocated {allocations} nodes (logarithmic bound {bound})"
        );
    }
}
