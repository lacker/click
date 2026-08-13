use super::*;

#[derive(Clone, Copy, Debug)]
struct ScalingSample {
    size: usize,
    work: usize,
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
        "{axis}: deterministic work grows faster than the simple-verification contract: {samples:?}"
    );
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

fn theorem_with_many_spellings(spelling_count: usize) -> String {
    let mut requirements = String::new();
    for zero_count in 0..spelling_count {
        let expression = format!("target{}", " + 0".repeat(zero_count));
        requirements.push_str(&format!("    requires {expression} == 7;\n"));
    }
    format!(
        "theorem surface_spelling_scaling(target: int32) {{\n{requirements}    ensures target == 7 by {{ assumption(); }}\n}}\n"
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
        click_source.push_str(&format!("resource member_{index}(value: int32);\n"));
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
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &source_refs)
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} simple scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), size);
            ScalingSample { size, work }
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
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
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
            ScalingSample { size, work }
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
                let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                    verify_c0_sources(&click_source, &[("straight.c", c_source.as_str())])
                });
                verified.unwrap_or_else(|error| {
                    panic!(
                        "size {size} straight-line fixture (snapshot={snapshot_claim}) failed: {}",
                        error.message()
                    )
                });
                ScalingSample { size, work }
            })
            .collect::<Vec<_>>();
        assert_near_linear_scaling("straight-line simple steps", &samples);
    }
}

#[test]
fn exact_assumption_scales_near_linearly_with_unrelated_ambient_facts() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let source = theorem_with_unrelated_exact_facts(size);
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_click_theorems(&source)
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} exact-fact scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), 1);
            ScalingSample { size, work }
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("exact assumption with unrelated facts", &samples);
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
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &[("exact_fact_target.c", c_source.as_str())])
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} explicit-step scaling fixture failed: {}",
                    error.message()
                )
            });
            ScalingSample { size, work }
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
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
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
            ScalingSample { size, work }
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("explicit transport with unrelated facts", &samples);
}

#[test]
fn same_kernel_fact_with_many_surface_spellings_scales_near_linearly() {
    let samples = [4, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let source = theorem_with_many_spellings(size);
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_click_theorems(&source)
            });
            verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} surface-spelling scaling fixture failed: {}",
                    error.message()
                )
            });
            ScalingSample { size, work }
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("same kernel fact with many surface spellings", &samples);
}

#[test]
fn grouped_claims_share_one_execution_with_near_linear_work() {
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let (c_source, click_source) = grouped_claim_project(size);
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &[("shared_claims.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} shared-claim scaling fixture failed: {}",
                    error.message()
                )
            });
            assert_eq!(verified.len(), size);
            ScalingSample { size, work }
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
            let (verified, work) = crate::instrumentation::measure_deterministic_work(|| {
                verify_c0_sources(&click_source, &[("preserve_bundle.c", c_source.as_str())])
            });
            let verified = verified.unwrap_or_else(|error| {
                panic!(
                    "size {size} resource-member scaling fixture failed: {}",
                    error.message()
                )
            });
            assert!(!verified.is_empty());
            ScalingSample { size, work }
        })
        .collect::<Vec<_>>();

    assert_near_linear_scaling("composite definition members", &samples);
}

#[test]
fn scaling_assertion_rejects_a_quadratic_curve() {
    let quadratic = [16, 32, 64, 128]
        .into_iter()
        .map(|size| ScalingSample {
            size,
            work: size * size,
        })
        .collect::<Vec<_>>();
    assert!(!near_linear_scaling(&quadratic));
}
