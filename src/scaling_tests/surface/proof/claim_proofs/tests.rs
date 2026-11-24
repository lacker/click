// Scaling tests of `src/surface/proof/claim_proofs.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

#[test]
fn explicit_closers_lower_each_return_goal_once_without_unfoldings() {
    use crate::instrumentation::{VerificationEvent, collect, measure_deterministic_work};
    crate::surface::verify_c_sources("theorem warm() { ensures true by normalize(); }", &[])
        .unwrap();
    for size in [2, 4, 8, 16] {
        let claims = "ensures result == x;\n".repeat(size);
        let closers = "close();\n".repeat(size);
        let source = format!(
            "verifying \"echo.c\"; int32 echo(int32 x) {{ {claims} }} by {{ step(); {closers} }}"
        );
        let ((verified, events), work) = measure_deterministic_work(|| {
            collect(|| {
                crate::surface::verify_c_sources(
                    &source,
                    &[("echo.c", "int32 echo(int32 x) { return x; }")],
                )
            })
        });
        assert_eq!(verified.unwrap().len(), size);
        let lowerings = events
            .iter()
            .filter(|event| {
                matches!(event,
                    VerificationEvent::OperationFinished { function, name, .. }
                        if function == "echo" && name == "return claim goal lowering"
                )
            })
            .count();
        eprintln!("return-goal lowerings: claims={size}, lowerings={lowerings}, work={work}");
        assert_eq!(lowerings, size, "each exact closer needs one goal lowering");
    }
}

fn check_return_claim_preparation_scaling(
    closer: &str,
    sizes: impl IntoIterator<Item = (usize, usize)>,
) {
    use crate::instrumentation::{VerificationEvent, collect};
    crate::surface::verify_c_sources("theorem warm() { ensures true by normalize(); }", &[])
        .unwrap();
    for (resources, claims) in sizes {
        let holdings = (0..resources)
            .map(|i| format!("owns marker({i});\n"))
            .collect::<String>();
        let ensures = "ensures result == x;\n".repeat(claims);
        // One closer per goal, in contract order: each held resource
        // first, then each proposition claim with the closer under test.
        let closers = format!("{}{}", "close();".repeat(resources), closer.repeat(claims));
        let source = format!(
            "resource marker(n: int32) {{ fact n == n; }}
         verifying \"echo.c\";
         int32 echo(int32 x) {{ {holdings}{ensures} }}
         by {{ step(); {closers} }}"
        );
        let (verified, events) = collect(|| {
            crate::surface::verify_c_sources(
                &source,
                &[("echo.c", "int32 echo(int32 x) { return x; }")],
            )
        });
        assert_eq!(verified.unwrap().len(), claims + resources);
        // Preparation is nested inside the first lowering; count only
        // the enclosing lowerings so no work is counted twice.
        let work = events
            .iter()
            .filter_map(|event| match event {
                VerificationEvent::OperationFinished {
                    function,
                    name,
                    work,
                    ..
                } if function == "echo" && name == "return claim goal lowering" => Some(*work),
                _ => None,
            })
            .sum::<usize>();
        eprintln!(
            "return views: closer={closer} resources={resources} claims={claims} work={work}"
        );
        assert!(
            work <= 12 * resources + 32 * claims,
            "return views must cost O(resources + claims): closer={closer}, resources={resources}, claims={claims}, work={work}"
        );
        if resources == 32 {
            assert!(
                work + resources * resources > 12 * resources + 32 * claims,
                "the smaller resource fixture must reject a quadratic preparation scan"
            );
        }
    }
}

#[test]
fn return_known_views_scale_with_resources_and_claims() {
    check_return_claim_preparation_scaling("close();", [1, 2, 4, 8].map(|size| (size, size)));
}

#[test]
fn return_normalization_views_scale_with_resources_and_claims() {
    check_return_claim_preparation_scaling("normalize();", [1, 2, 4, 8].map(|size| (size, size)));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: full 24-case resource/claim matrix took 10.38s beside release compilation"]
fn exact_return_closers_share_preparation_beside_unrelated_resources() {
    // Keep all 24 combinations, both closers, the empty-resource case,
    // and all claim counts. A tighter resource allowance above also
    // rejects an added quadratic scan at the smaller largest input.
    for closer in ["close();", "normalize();"] {
        check_return_claim_preparation_scaling(
            closer,
            [0, 4, 16, 32]
                .into_iter()
                .flat_map(|resources| [1, 4, 16].map(move |claims| (resources, claims))),
        );
    }
}

/// Post-execution `have` steps before the fold of a produced resource, the
/// shape of the generic stack's `pop` proof. Before each `have` the proof
/// retries the contract's return-resource transition, which fails until the
/// fold. The retry reads the outcome's resources against the facts, so the
/// outcome's memory index must advance with the facts each `have` adds:
/// pairing every fact since execution ended made the `have` at position `k`
/// cost about nine units per earlier `have`, quadratic over the proof.
#[test]
fn post_execution_haves_before_a_fold_cost_the_same_at_every_position() {
    use crate::instrumentation::collect_tactic_work;
    crate::surface::verify_c_sources("theorem warm() { ensures true by normalize(); }", &[])
        .unwrap();
    let mut last_works = Vec::new();
    for size in [4, 8, 12, 16] {
        let parameters = (1..=size)
            .map(|i| format!(", int x{i}"))
            .collect::<String>();
        let click_parameters = (1..=size)
            .map(|i| format!(", int32 x{i}"))
            .collect::<String>();
        let bounds = (1..=size)
            .map(|i| format!("requires x{i} >= {i};\nrequires x{i} <= {i};\n"))
            .collect::<String>();
        let haves = (1..=size)
            .map(|i| {
                format!("have x{i} == {i} by normalize() using {{ x{i} >= {i}; x{i} <= {i}; }};\n")
            })
            .collect::<String>();
        let c = format!(
            "struct cell {{ int value; }};\nstruct holder {{ struct cell *first; }};\nvoid write(struct holder *h, int x{parameters}) {{ h->first->value = x; }}\n"
        );
        let source = format!(
            "verifying \"cell.c\";
resource cell_at(c: struct cell*) {{ field value: int32; owns c->value; fact c->value == value; }}
void write(struct holder* h, int32 x{click_parameters}) {{
    owns h->first;
    consumes before: cell_at(h->first);
    produces after: cell_at(h->first);
    {bounds}
    ensures after.value == x;
}} by {{
    let {{}} = unfold(before);
    step_until(function.exit);
    {haves}
    let after = fold(cell_at(h->first), {{ value: x }});
}}"
        );
        let (verified, samples) = collect_tactic_work(|| {
            crate::surface::verify_c_sources(&source, &[("cell.c", c.as_str())])
        });
        verified.unwrap_or_else(|error| panic!("size {size}: {error}"));
        let works = samples
            .iter()
            .filter(|sample| sample.tactic.tactic_name == "have")
            .map(|sample| sample.work)
            .collect::<Vec<_>>();
        eprintln!("haves before a fold: size={size}, works={works:?}");
        assert_eq!(works.len(), size);
        // The first two `have`s warm the outcome's index; from the third on
        // each pairs one `have`'s facts.
        let settled = &works[2..];
        let (low, high) = (
            *settled.iter().min().unwrap(),
            *settled.iter().max().unwrap(),
        );
        assert!(
            high <= low + 4,
            "a `have` before the fold must not cost more at a later position: size={size}, works={works:?}"
        );
        last_works.push(works[size - 1]);
    }
    assert!(
        last_works[3] <= last_works[0] + 4,
        "the last `have` must cost the same at every size: {last_works:?}"
    );
}
